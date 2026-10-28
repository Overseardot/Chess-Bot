// ============================================================
//  Chess Bot — a single-file UCI chess engine
//  Compile: g++ -O3 -march=native -std=c++17 -pthread ChessBot.cpp -o ChessBot
// ============================================================
#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <sstream>
#include <string>
#include <thread>
#include <vector>
#include <cctype>

using namespace std;
typedef uint64_t U64;

// ------------------------- Constants -------------------------
enum { WHITE = 0, BLACK = 1 };
enum { PAWN = 0, KNIGHT, BISHOP, ROOK, QUEEN, KING };

const int INF       = 32001;
const int MATE      = 32000;
const int MAX_PLY   = 128;

const int FLAG_EP     = 1;
const int FLAG_CASTLE = 2;
const int FLAG_DOUBLE = 4;

// piece values (used for ordering / delta pruning)
const int pieceValue[6] = { 100, 320, 330, 500, 900, 20000 };

// castling bits
enum { CWK = 1, CWQ = 2, CBK = 4, CBQ = 8 };

inline int popcount(U64 b) { return __builtin_popcountll(b); }
inline int poplsb(U64 &b) { int s = __builtin_ctzll(b); b &= b - 1; return s; }
inline void setBit(U64 &b, int s)   { b |=  (1ULL << s); }
inline void clearBit(U64 &b, int s) { b &= ~(1ULL << s); }

// ------------------------- Move -------------------------
struct Move {
    uint8_t from = 0, to = 0, promo = 0, flags = 0;
    Move() = default;
    Move(int f, int t, int p, int fl) : from(f), to(t), promo(p), flags(fl) {}
    bool isNull() const { return from == 0 && to == 0 && promo == 0; }
    bool operator==(const Move &o) const {
        return from == o.from && to == o.to && promo == o.promo;
    }
};

struct MoveList {
    Move moves[256];
    int  scores[256];
    int  count = 0;
    void add(int f, int t, int p = 0, int fl = 0) { moves[count++] = Move(f, t, p, fl); }
};

// ------------------------- Board state -------------------------
U64 byType[2][6];
U64 byColor[2];
U64 all;

int mailbox[64];
int side;
int castling;
int ep;
int fifty;
int kingSq[2];
U64 hashKey;

struct Undo {
    int captured, capSq, castling, ep, fifty;
    U64 hash;
};
Undo undoStack[2048];
int  undoCount = 0;

U64  posHistory[2048];
int  posCount = 0;

int  castleMask[64];

// Zobrist
U64 zPiece[12][64];
U64 zCastle[16];
U64 zEp[8];
U64 zSide;

// ------------------------- Attack tables -------------------------
U64 knightAtt[64], kingAtt[64], pawnAtt[2][64];
U64 fileMask[8];
U64 passedMask[2][64];   // squares that must be free of enemy pawns for a passed pawn

const int rookDr[4]   = {1, -1, 0, 0};
const int rookDf[4]   = {0, 0, 1, -1};
const int bishopDr[4] = {1, 1, -1, -1};
const int bishopDf[4] = {1, -1, 1, -1};

inline U64 slidingAttacks(int sq, U64 occ, const int *dr, const int *df, int n) {
    U64 att = 0;
    int r = sq >> 3, f = sq & 7;
    for (int i = 0; i < n; ++i) {
        int rr = r + dr[i], ff = f + df[i];
        while (rr >= 0 && rr < 8 && ff >= 0 && ff < 8) {
            int s = rr * 8 + ff;
            att |= 1ULL << s;
            if (occ & (1ULL << s)) break;
            rr += dr[i]; ff += df[i];
        }
    }
    return att;
}
inline U64 rookAttacks(int sq, U64 occ)   { return slidingAttacks(sq, occ, rookDr, rookDf, 4); }
inline U64 bishopAttacks(int sq, U64 occ) { return slidingAttacks(sq, occ, bishopDr, bishopDf, 4); }

bool isSquareAttacked(int sq, int by) {
    if (pawnAtt[by ^ 1][sq] & byType[by][PAWN])   return true;
    if (knightAtt[sq]       & byType[by][KNIGHT]) return true;
    if (kingAtt[sq]         & byType[by][KING])   return true;
    if (bishopAttacks(sq, all) & (byType[by][BISHOP] | byType[by][QUEEN])) return true;
    if (rookAttacks(sq, all)   & (byType[by][ROOK]   | byType[by][QUEEN])) return true;
    return false;
}

// ------------------------- Init -------------------------
void initTables() {
    memset(byType, 0, sizeof(byType));
    memset(byColor, 0, sizeof(byColor));

    for (int i = 0; i < 64; i++) castleMask[i] = 15;
    castleMask[4]  = 15 & ~3;
    castleMask[0]  = 15 & ~2;
    castleMask[7]  = 15 & ~1;
    castleMask[60] = 15 & ~12;
    castleMask[56] = 15 & ~8;
    castleMask[63] = 15 & ~4;

    // pseudo-random generator for Zobrist keys
    U64 seed = 0x9E3779B97F4A7C15ULL;
    auto rnd = [&]() {
        seed ^= seed >> 12; seed ^= seed << 25; seed ^= seed >> 27;
        return seed * 2685821657736338717ULL;
    };
    for (int p = 0; p < 12; p++)
        for (int s = 0; s < 64; s++) zPiece[p][s] = rnd();
    for (int i = 0; i < 16; i++) zCastle[i] = rnd();
    for (int i = 0; i < 8; i++)  zEp[i] = rnd();
    zSide = rnd();

    for (int s = 0; s < 64; s++) {
        int r = s >> 3, f = s & 7;
        knightAtt[s] = kingAtt[s] = 0;
        const int kn[8][2] = {{1,2},{2,1},{-1,2},{-2,1},{1,-2},{2,-1},{-1,-2},{-2,-1}};
        for (auto &d : kn) {
            int rr = r + d[0], ff = f + d[1];
            if (rr >= 0 && rr < 8 && ff >= 0 && ff < 8) knightAtt[s] |= 1ULL << (rr*8+ff);
        }
        for (int dr = -1; dr <= 1; dr++)
            for (int df = -1; df <= 1; df++) {
                if (!dr && !df) continue;
                int rr = r + dr, ff = f + df;
                if (rr >= 0 && rr < 8 && ff >= 0 && ff < 8) kingAtt[s] |= 1ULL << (rr*8+ff);
            }
    }
    for (int s = 0; s < 64; s++) {
        int r = s >> 3, f = s & 7;
        pawnAtt[WHITE][s] = pawnAtt[BLACK][s] = 0;
        if (r < 7) {
            if (f > 0) pawnAtt[WHITE][s] |= 1ULL << (s + 7);
            if (f < 7) pawnAtt[WHITE][s] |= 1ULL << (s + 9);
        }
        if (r > 0) {
            if (f > 0) pawnAtt[BLACK][s] |= 1ULL << (s - 9);
            if (f < 7) pawnAtt[BLACK][s] |= 1ULL << (s - 7);
        }
    }
    for (int f = 0; f < 8; f++) fileMask[f] = 0x0101010101010101ULL << f;

    for (int s = 0; s < 64; s++) {
        int r = s >> 3, f = s & 7;
        for (int c = 0; c < 2; c++) passedMask[c][s] = 0;
        U64 front = 0, mask = 0;
        if (r < 7) front = ~0ULL << ((r + 1) * 8);
        mask = fileMask[f];
        if (f > 0) mask |= fileMask[f - 1];
        if (f < 7) mask |= fileMask[f + 1];
        passedMask[WHITE][s] = front & mask;
        U64 back = (r > 0) ? ((1ULL << (r * 8)) - 1) : 0;
        passedMask[BLACK][s] = back & mask;
    }
}

// ------------------------- Board helpers -------------------------
inline void addPiece(int sq, int pc) {
    setBit(byType[pc / 6][pc % 6], sq);
    setBit(byColor[pc / 6], sq);
    setBit(all, sq);
    mailbox[sq] = pc;
    if (pc % 6 == KING) kingSq[pc / 6] = sq;
}

void setFen(const string &fen) {
    memset(byType, 0, sizeof(byType));
    memset(byColor, 0, sizeof(byColor));
    all = 0;
    for (int i = 0; i < 64; i++) mailbox[i] = -1;
    castling = 0; ep = -1; fifty = 0; undoCount = 0;

    istringstream ss(fen);
    string bstr, sstr, cstr, estr;
    ss >> bstr >> sstr >> cstr >> estr >> fifty;

    int r = 7, f = 0;
    for (char c : bstr) {
        if (c == '/') { r--; f = 0; }
        else if (isdigit(c)) f += c - '0';
        else {
            int color = isupper(c) ? WHITE : BLACK;
            char l = tolower(c);
            int type = (l == 'p') ? PAWN : (l == 'n') ? KNIGHT : (l == 'b') ? BISHOP
                     : (l == 'r') ? ROOK : (l == 'q') ? QUEEN : KING;
            addPiece(r * 8 + f, color * 6 + type);
            f++;
        }
    }
    side = (sstr == "w") ? WHITE : BLACK;
    for (char c : cstr) {
        if (c == 'K') castling |= CWK;
        else if (c == 'Q') castling |= CWQ;
        else if (c == 'k') castling |= CBK;
        else if (c == 'q') castling |= CBQ;
    }
    if (estr != "-" && estr.size() >= 2)
        ep = (estr[1] - '1') * 8 + (estr[0] - 'a');

    hashKey = 0;
    for (int p = 0; p < 12; p++) {
        U64 b = byType[p / 6][p % 6];
        while (b) { int s = poplsb(b); hashKey ^= zPiece[p][s]; }
    }
    hashKey ^= zCastle[castling];
    // Match makeMove(): only hash en-passant when a capture is available.
    if (ep >= 0 && (pawnAtt[side ^ 1][ep] & byType[side][PAWN]))
        hashKey ^= zEp[ep & 7];
    if (side == BLACK) hashKey ^= zSide;

    posCount = 0;
    posHistory[posCount++] = hashKey;
}

string moveToStr(Move m) {
    if (m.isNull()) return "0000";
    string s;
    s += char('a' + (m.from & 7));
    s += char('1' + (m.from >> 3));
    s += char('a' + (m.to & 7));
    s += char('1' + (m.to >> 3));
    if (m.promo) s += " nbrq"[m.promo];
    return s;
}

// ------------------------- Move generation -------------------------
void addPromotions(MoveList &ml, int from, int to) {
    ml.add(from, to, QUEEN);
    ml.add(from, to, ROOK);
    ml.add(from, to, BISHOP);
    ml.add(from, to, KNIGHT);
}

void generateMoves(MoveList &ml, bool capturesOnly) {
    int us = side, them = us ^ 1;
    U64 occ = all, ours = byColor[us], theirs = byColor[them];

    // ---- pawns ----
    U64 b = byType[us][PAWN];
    int fwd = (us == WHITE) ? 8 : -8;
    int startRank = (us == WHITE) ? 1 : 6;
    int promoRank = (us == WHITE) ? 6 : 1;
    while (b) {
        int s = poplsb(b);
        int r = s >> 3, f = s & 7;
        int t = s + fwd;
        if (t >= 0 && t < 64 && !(occ & (1ULL << t))) {
            if (r == promoRank) addPromotions(ml, s, t);
            else if (!capturesOnly) {
                ml.add(s, t);
                if (r == startRank && !(occ & (1ULL << (t + fwd))))
                    ml.add(s, t + fwd, 0, FLAG_DOUBLE);
            }
        }
        for (int df = -1; df <= 1; df += 2) {
            int ff = f + df;
            if (ff < 0 || ff > 7) continue;
            int tt = s + fwd + df;
            if (tt < 0 || tt > 63) continue;
            if (theirs & (1ULL << tt)) {
                if (r == promoRank) addPromotions(ml, s, tt);
                else ml.add(s, tt);
            } else if (tt == ep) {
                ml.add(s, tt, 0, FLAG_EP);
            }
        }
    }

    // ---- knights ----
    b = byType[us][KNIGHT];
    while (b) {
        int s = poplsb(b);
        U64 att = knightAtt[s] & ~ours;
        while (att) {
            int t = poplsb(att);
            if (!capturesOnly || (theirs & (1ULL << t))) ml.add(s, t);
        }
    }

    // ---- bishops / rooks / queens ----
    for (int pt = BISHOP; pt <= QUEEN; pt++) {
        b = byType[us][pt];
        while (b) {
            int s = poplsb(b);
            U64 att = (pt == BISHOP ? bishopAttacks(s, occ)
                     : pt == ROOK   ? rookAttacks(s, occ)
                     : bishopAttacks(s, occ) | rookAttacks(s, occ)) & ~ours;
            while (att) {
                int t = poplsb(att);
                if (!capturesOnly || (theirs & (1ULL << t))) ml.add(s, t);
            }
        }
    }

    // ---- king ----
    int ks = kingSq[us];
    U64 att = kingAtt[ks] & ~ours;
    while (att) {
        int t = poplsb(att);
        if (!capturesOnly || (theirs & (1ULL << t))) ml.add(ks, t);
    }

    // ---- castling ----
    if (!capturesOnly) {
        if (us == WHITE) {
            if ((castling & CWK) && !(occ & ((1ULL<<5)|(1ULL<<6)))
                && (mailbox[7] == WHITE*6+ROOK)
                && !isSquareAttacked(4, BLACK) && !isSquareAttacked(5, BLACK)
                && !isSquareAttacked(6, BLACK))
                ml.add(4, 6, 0, FLAG_CASTLE);
            if ((castling & CWQ) && !(occ & ((1ULL<<1)|(1ULL<<2)|(1ULL<<3)))
                && (mailbox[0] == WHITE*6+ROOK)
                && !isSquareAttacked(4, BLACK) && !isSquareAttacked(3, BLACK)
                && !isSquareAttacked(2, BLACK))
                ml.add(4, 2, 0, FLAG_CASTLE);
        } else {
            if ((castling & CBK) && !(occ & ((1ULL<<61)|(1ULL<<62)))
                && (mailbox[63] == BLACK*6+ROOK)
                && !isSquareAttacked(60, WHITE) && !isSquareAttacked(61, WHITE)
                && !isSquareAttacked(62, WHITE))
                ml.add(60, 62, 0, FLAG_CASTLE);
            if ((castling & CBQ) && !(occ & ((1ULL<<57)|(1ULL<<58)|(1ULL<<59)))
                && (mailbox[56] == BLACK*6+ROOK)
                && !isSquareAttacked(60, WHITE) && !isSquareAttacked(59, WHITE)
                && !isSquareAttacked(58, WHITE))
                ml.add(60, 58, 0, FLAG_CASTLE);
        }
    }
}

// ------------------------- Make / unmake -------------------------
void makeMove(Move m) {
    Undo &u = undoStack[undoCount++];
    u.castling = castling;
    u.ep = ep;
    u.fifty = fifty;
    u.hash = hashKey;

    int us = side, them = us ^ 1;
    int from = m.from, to = m.to;
    int pc = mailbox[from];

    int capSq = to;
    if (m.flags & FLAG_EP) capSq = (us == WHITE) ? to - 8 : to + 8;
    int captured = mailbox[capSq];
    u.captured = captured;
    u.capSq = capSq;

    if (captured >= 0) {
        int cc = captured / 6, ct = captured % 6;
        clearBit(byType[cc][ct], capSq);
        clearBit(byColor[cc], capSq);
        clearBit(all, capSq);
        mailbox[capSq] = -1;
        hashKey ^= zPiece[captured][capSq];
        fifty = 0;
    } else fifty++;

    int ptype = pc % 6;
    clearBit(byType[us][ptype], from);
    clearBit(byColor[us], from);
    clearBit(all, from);
    mailbox[from] = -1;
    hashKey ^= zPiece[pc][from];

    int newPc = m.promo ? (us * 6 + m.promo) : pc;
    setBit(byType[us][newPc % 6], to);
    setBit(byColor[us], to);
    setBit(all, to);
    mailbox[to] = newPc;
    hashKey ^= zPiece[newPc][to];

    if (ptype == PAWN) fifty = 0;
    if (ptype == KING) kingSq[us] = to;

    if (m.flags & FLAG_CASTLE) {
        int rf, rt;
        if      (to ==  6) { rf =  7; rt =  5; }
        else if (to ==  2) { rf =  0; rt =  3; }
        else if (to == 62) { rf = 63; rt = 61; }
        else               { rf = 56; rt = 59; }
        int rook = mailbox[rf];
        clearBit(byType[us][ROOK], rf); clearBit(byColor[us], rf);
        clearBit(all, rf); mailbox[rf] = -1;
        setBit(byType[us][ROOK], rt); setBit(byColor[us], rt);
        setBit(all, rt); mailbox[rt] = rook;
        hashKey ^= zPiece[rook][rf] ^ zPiece[rook][rt];
    }

    int nc = castling & castleMask[from] & castleMask[to];
    if (nc != castling) {
        hashKey ^= zCastle[castling] ^ zCastle[nc];
        castling = nc;
    }

    if (ep >= 0) hashKey ^= zEp[ep & 7];
    ep = -1;
    if (m.flags & FLAG_DOUBLE) {
        int e = (us == WHITE) ? from + 8 : from - 8;
        if (pawnAtt[us][e] & byType[them][PAWN]) {
            ep = e;
            hashKey ^= zEp[e & 7];
        }
    }

    side = them;
    hashKey ^= zSide;
    posHistory[posCount++] = hashKey;
}

void unmakeMove(Move m) {
    Undo &u = undoStack[--undoCount];
    side ^= 1;
    int us = side;
    int from = m.from, to = m.to;
    int pc = mailbox[to];
    int ptype = pc % 6;

    clearBit(byType[us][ptype], to);
    clearBit(byColor[us], to);
    clearBit(all, to);
    mailbox[to] = -1;

    int origPc = m.promo ? (us * 6 + PAWN) : pc;
    setBit(byType[us][origPc % 6], from);
    setBit(byColor[us], from);
    setBit(all, from);
    mailbox[from] = origPc;

    if (ptype == KING) kingSq[us] = from;

    if (u.captured >= 0) {
        int cs = u.capSq;
        int cc = u.captured / 6, ct = u.captured % 6;
        setBit(byType[cc][ct], cs);
        setBit(byColor[cc], cs);
        setBit(all, cs);
        mailbox[cs] = u.captured;
    }

    if (m.flags & FLAG_CASTLE) {
        int rf, rt;
        if      (to ==  6) { rf =  7; rt =  5; }
        else if (to ==  2) { rf =  0; rt =  3; }
        else if (to == 62) { rf = 63; rt = 61; }
        else               { rf = 56; rt = 59; }
        int rook = mailbox[rt];
        clearBit(byType[us][ROOK], rt); clearBit(byColor[us], rt);
        clearBit(all, rt); mailbox[rt] = -1;
        setBit(byType[us][ROOK], rf); setBit(byColor[us], rf);
        setBit(all, rf); mailbox[rf] = rook;
    }

    castling = u.castling;
    ep = u.ep;
    fifty = u.fifty;
    hashKey = u.hash;
    posCount--;
}

void makeNullMove() {
    Undo &u = undoStack[undoCount++];
    u.castling = castling; u.ep = ep; u.fifty = fifty; u.hash = hashKey;
    u.captured = -1; u.capSq = -1;
    if (ep >= 0) hashKey ^= zEp[ep & 7];
    ep = -1;
    fifty++;
    side ^= 1;
    hashKey ^= zSide;
    posHistory[posCount++] = hashKey;
}

void unmakeNullMove() {
    Undo &u = undoStack[--undoCount];
    side ^= 1;
    castling = u.castling; ep = u.ep; fifty = u.fifty; hashKey = u.hash;
    posCount--;
}

bool isLegal(Move m) {
    makeMove(m);
    bool ok = !isSquareAttacked(kingSq[side ^ 1], side);
    unmakeMove(m);
    return ok;
}

// ------------------------- Evaluation -------------------------
static const int pawnMG[64] = {
     0,  0,  0,  0,  0,  0,  0,  0,
    50, 50, 50, 50, 50, 50, 50, 50,
    10, 10, 20, 30, 30, 20, 10, 10,
     5,  5, 10, 25, 25, 10,  5,  5,
     0,  0,  0, 20, 20,  0,  0,  0,
     5, -5,-10,  0,  0,-10, -5,  5,
     5, 10, 10,-20,-20, 10, 10,  5,
     0,  0,  0,  0,  0,  0,  0,  0
};
static const int pawnEG[64] = {
     0,  0,  0,  0,  0,  0,  0,  0,
    80, 80, 80, 80, 80, 80, 80, 80,
    50, 50, 50, 50, 50, 50, 50, 50,
    30, 30, 30, 30, 30, 30, 30, 30,
    15, 15, 15, 15, 15, 15, 15, 15,
     5,  5,  5,  5,  5,  5,  5,  5,
     0,  0,  0,  0,  0,  0,  0,  0,
     0,  0,  0,  0,  0,  0,  0,  0
};
static const int knightMG[64] = {
   -50,-40,-30,-30,-30,-30,-40,-50,
   -40,-20,  0,  0,  0,  0,-20,-40,
   -30,  0, 10, 15, 15, 10,  0,-30,
   -30,  5, 15, 20, 20, 15,  5,-30,
   -30,  0, 15, 20, 20, 15,  0,-30,
   -30,  5, 10, 15, 15, 10,  5,-30,
   -40,-20,  0,  5,  5,  0,-20,-40,
   -50,-40,-30,-30,-30,-30,-40,-50
};
static const int knightEG[64] = {
   -50,-40,-30,-30,-30,-30,-40,-50,
   -40,-20,  0,  0,  0,  0,-20,-40,
   -30,  0, 10, 15, 15, 10,  0,-30,
   -30,  5, 15, 20, 20, 15,  5,-30,
   -30,  0, 15, 20, 20, 15,  0,-30,
   -30,  5, 10, 15, 15, 10,  5,-30,
   -40,-20,  0,  5,  5,  0,-20,-40,
   -50,-40,-30,-30,-30,-30,-40,-50
};
static const int bishopMG[64] = {
   -20,-10,-10,-10,-10,-10,-10,-20,
   -10,  0,  0,  0,  0,  0,  0,-10,
   -10,  0,  5, 10, 10,  5,  0,-10,
   -10,  5,  5, 10, 10,  5,  5,-10,
   -10,  0, 10, 10, 10, 10,  0,-10,
   -10, 10, 10, 10, 10, 10, 10,-10,
   -10,  5,  0,  0,  0,  0,  5,-10,
   -20,-10,-10,-10,-10,-10,-10,-20
};
static const int bishopEG[64] = {
   -20,-10,-10,-10,-10,-10,-10,-20,
   -10,  0,  0,  0,  0,  0,  0,-10,
   -10,  0,  5, 10, 10,  5,  0,-10,
   -10,  5,  5, 10, 10,  5,  5,-10,
   -10,  0, 10, 10, 10, 10,  0,-10,
   -10, 10, 10, 10, 10, 10, 10,-10,
   -10,  5,  0,  0,  0,  0,  5,-10,
   -20,-10,-10,-10,-10,-10,-10,-20
};
static const int rookMG[64] = {
     0,  0,  0,  0,  0,  0,  0,  0,
     5, 10, 10, 10, 10, 10, 10,  5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
     0,  0,  0,  5,  5,  0,  0,  0
};
static const int rookEG[64] = {
     0,  0,  0,  0,  0,  0,  0,  0,
     5, 10, 10, 10, 10, 10, 10,  5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
    -5,  0,  0,  0,  0,  0,  0, -5,
     0,  0,  0,  5,  5,  0,  0,  0
};
static const int queenMG[64] = {
   -20,-10,-10, -5, -5,-10,-10,-20,
   -10,  0,  0,  0,  0,  0,  0,-10,
   -10,  0,  5,  5,  5,  5,  0,-10,
    -5,  0,  5,  5,  5,  5,  0, -5,
     0,  0,  5,  5,  5,  5,  0, -5,
   -10,  5,  5,  5,  5,  5,  0,-10,
   -10,  0,  5,  0,  0,  0,  0,-10,
   -20,-10,-10, -5, -5,-10,-10,-20
};
static const int queenEG[64] = {
   -20,-10,-10, -5, -5,-10,-10,-20,
   -10,  0,  0,  0,  0,  0,  0,-10,
   -10,  0,  5,  5,  5,  5,  0,-10,
    -5,  0,  5,  5,  5,  5,  0, -5,
     0,  0,  5,  5,  5,  5,  0, -5,
   -10,  5,  5,  5,  5,  5,  0,-10,
   -10,  0,  5,  0,  0,  0,  0,-10,
   -20,-10,-10, -5, -5,-10,-10,-20
};
static const int kingMG[64] = {
   -30,-40,-40,-50,-50,-40,-40,-30,
   -30,-40,-40,-50,-50,-40,-40,-30,
   -30,-40,-40,-50,-50,-40,-40,-30,
   -30,-40,-40,-50,-50,-40,-40,-30,
   -20,-30,-30,-40,-40,-30,-30,-20,
   -10,-20,-20,-20,-20,-20,-20,-10,
    20, 20,  0,  0,  0,  0, 20, 20,
    20, 30, 10,  0,  0, 10, 30, 20
};
static const int kingEG[64] = {
   -50,-40,-30,-20,-20,-30,-40,-50,
   -30,-20,-10,  0,  0,-10,-20,-30,
   -30,-10, 20, 30, 30, 20,-10,-30,
   -30,-10, 30, 40, 40, 30,-10,-30,
   -30,-10, 30, 40, 40, 30,-10,-30,
   -30,-10, 20, 30, 30, 20,-10,-30,
   -30,-30,  0,  0,  0,  0,-30,-30,
   -50,-30,-30,-30,-30,-30,-30,-50
};

const int *mgPtr[6] = { pawnMG, knightMG, bishopMG, rookMG, queenMG, kingMG };
const int *egPtr[6] = { pawnEG, knightEG, bishopEG, rookEG, queenEG, kingEG };
const int mgVal[6] = { 100, 320, 330, 500, 900, 0 };
const int egVal[6] = { 120, 300, 320, 530, 950, 0 };

const int passedMG[8] = { 0,  5, 10, 20, 35, 60, 100, 0 };
const int passedEG[8] = { 0, 10, 20, 35, 60, 100, 160, 0 };

int evaluate() {
    int mg[2] = {0, 0}, eg[2] = {0, 0};
    int phase = 0;

    for (int c = 0; c < 2; c++) {
        for (int pt = 0; pt < 6; pt++) {
            U64 b = byType[c][pt];
            while (b) {
                int s = poplsb(b);
                int idx = (c == WHITE) ? (s ^ 56) : s;
                mg[c] += mgPtr[pt][idx] + mgVal[pt];
                eg[c] += egPtr[pt][idx] + egVal[pt];
            }
        }
        phase += 1 * popcount(byType[c][KNIGHT]);
        phase += 1 * popcount(byType[c][BISHOP]);
        phase += 2 * popcount(byType[c][ROOK]);
        phase += 4 * popcount(byType[c][QUEEN]);

        // bishop pair
        if (popcount(byType[c][BISHOP]) >= 2) { mg[c] += 25; eg[c] += 40; }
    }
    phase = min(phase, 16);

    // pawn structure
    for (int c = 0; c < 2; c++) {
        U64 myPawns  = byType[c][PAWN];
        U64 oppPawns = byType[c ^ 1][PAWN];
        U64 bb = myPawns;
        while (bb) {
            int s = poplsb(bb);
            int f = s & 7, r = s >> 3;
            int relRank = (c == WHITE) ? r : 7 - r;

            // doubled
            int fileCnt = popcount(myPawns & fileMask[f]);
            if (fileCnt > 1) { mg[c] -= 10; eg[c] -= 20; }

            // isolated
            U64 adj = 0;
            if (f > 0) adj |= fileMask[f - 1];
            if (f < 7) adj |= fileMask[f + 1];
            if (!(myPawns & adj)) { mg[c] -= 15; eg[c] -= 10; }

            // passed
            if (!(oppPawns & passedMask[c][s])) {
                mg[c] += passedMG[relRank];
                eg[c] += passedEG[relRank];
            }
        }
    }

    int mgScore = mg[WHITE] - mg[BLACK];
    int egScore = eg[WHITE] - eg[BLACK];
    int score = (mgScore * phase + egScore * (16 - phase)) / 16;
    return (side == WHITE) ? score : -score;
}

// ------------------------- Transposition table -------------------------
struct TTEntry {
    U64 key = 0;
    int32_t score = 0;
    uint16_t move = 0;
    uint8_t depth = 0;
    uint8_t flag = 0;   // 0 empty, 1 exact, 2 upper, 3 lower
};
// Power-of-two table size, so a position hashes to one TT slot cheaply.
// The advertised Hash option is implemented in megabytes.
size_t TT_SIZE = size_t(1) << 22; // 64 MiB with the current TTEntry layout
vector<TTEntry> TT;

void clearTT() { fill(TT.begin(), TT.end(), TTEntry()); }

void resizeHash(int megabytes) {
    megabytes = max(1, min(megabytes, 1024));
    size_t targetEntries = (size_t(megabytes) * 1024 * 1024) / sizeof(TTEntry);
    size_t entries = size_t(1) << 16;
    while ((entries << 1) <= targetEntries) entries <<= 1;
    TT_SIZE = entries;
    TT.assign(TT_SIZE, TTEntry{});
}

uint16_t encodeMove(Move m) {
    return (uint16_t)(m.from | (m.to << 6) | (m.promo << 12));
}
Move decodeMove(uint16_t v) {
    return Move(v & 63, (v >> 6) & 63, (v >> 12) & 7, 0);
}

// ------------------------- Search globals -------------------------
atomic<bool> stopSearch(false);
long long timeLimitMs = 0;
chrono::steady_clock::time_point searchStart;
U64 nodes = 0;

Move killers[2][MAX_PLY];
int  historyTable[64][64];
Move rootBest;

long long elapsedMs() {
    return chrono::duration_cast<chrono::milliseconds>(
        chrono::steady_clock::now() - searchStart).count();
}

void checkTime() {
    if (timeLimitMs > 0 && elapsedMs() >= timeLimitMs) stopSearch = true;
}

bool isRepetition() {
    for (int i = posCount - 3; i >= 0 && i >= posCount - 1 - fifty; i -= 2)
        if (posHistory[i] == hashKey) return true;
    return false;
}

bool hasNonPawnMaterial() {
    return (byType[side][KNIGHT] | byType[side][BISHOP] |
            byType[side][ROOK]   | byType[side][QUEEN]) != 0;
}

void scoreMoves(MoveList &ml, Move ttMove, int ply) {
    for (int i = 0; i < ml.count; i++) {
        Move m = ml.moves[i];
        if (!ttMove.isNull() && m == ttMove) { ml.scores[i] = 2000000; continue; }
        if (m.promo) { ml.scores[i] = 1500000 + pieceValue[m.promo]; continue; }
        if (m.flags & FLAG_EP) { ml.scores[i] = 1000000; continue; }
        if (mailbox[m.to] >= 0) {
            int victim   = pieceValue[mailbox[m.to] % 6];
            int attacker = pieceValue[mailbox[m.from] % 6];
            ml.scores[i] = 1000000 + victim * 16 - attacker;
            continue;
        }
        if (killers[0][ply] == m) { ml.scores[i] = 800000; continue; }
        if (killers[1][ply] == m) { ml.scores[i] = 799000; continue; }
        ml.scores[i] = historyTable[m.from][m.to];
    }
}

void pickBest(MoveList &ml, int i) {
    int best = i;
    for (int j = i + 1; j < ml.count; j++)
        if (ml.scores[j] > ml.scores[best]) best = j;
    swap(ml.moves[i], ml.moves[best]);
    swap(ml.scores[i], ml.scores[best]);
}

// ------------------------- Quiescence -------------------------
int quiescence(int alpha, int beta, int ply) {
    if (stopSearch) return 0;
    nodes++;
    if ((nodes & 1023) == 0) checkTime();
    if (stopSearch) return 0;
    if (ply >= MAX_PLY - 1) return evaluate();

    bool inCheck = isSquareAttacked(kingSq[side], side ^ 1);

    int best;
    if (inCheck) best = -MATE + ply;
    else {
        best = evaluate();
        if (best >= beta) return best;
        if (best > alpha) alpha = best;
    }

    MoveList ml;
    generateMoves(ml, !inCheck);
    scoreMoves(ml, Move(), ply);

    for (int i = 0; i < ml.count; i++) {
        pickBest(ml, i);
        Move m = ml.moves[i];

        int capVal = 0;
        if (m.flags & FLAG_EP) capVal = pieceValue[PAWN];
        else if (mailbox[m.to] >= 0) capVal = pieceValue[mailbox[m.to] % 6];

        if (!inCheck && !m.promo && best + capVal + 200 < alpha) continue;

        makeMove(m);
        if (isSquareAttacked(kingSq[side ^ 1], side)) { unmakeMove(m); continue; }

        int score = -quiescence(-beta, -alpha, ply + 1);
        unmakeMove(m);
        if (stopSearch) return 0;

        if (score > best) {
            best = score;
            if (score > alpha) alpha = score;
            if (alpha >= beta) break;
        }
    }
    return best;
}

// ------------------------- Main search -------------------------
int search(int depth, int alpha, int beta, int ply, bool nullOk) {
    if (stopSearch) return 0;

    if (depth <= 0) return quiescence(alpha, beta, ply);

    nodes++;
    if ((nodes & 1023) == 0) checkTime();
    if (stopSearch) return 0;

    if (ply >= MAX_PLY - 1) return evaluate();

    if (ply > 0) {
        if (isRepetition() || fifty >= 100) return 0;
        alpha = max(alpha, -MATE + ply);
        beta  = min(beta,   MATE - ply - 1);
        if (alpha >= beta) return alpha;
    }

    bool pvNode = (beta - alpha) > 1;
    bool inCheck = isSquareAttacked(kingSq[side], side ^ 1);
    if (inCheck) depth++;

    // ---- TT probe ----
    TTEntry &tte = TT[hashKey & (TT_SIZE - 1)];
    Move ttMove;
    int  ttScore = 0, ttDepth = 0, ttFlag = 0;
    if (tte.key == hashKey) {
        ttMove  = decodeMove(tte.move);
        ttScore = tte.score;
        ttDepth = tte.depth;
        ttFlag  = tte.flag;
        if (ply > 0 && ttDepth >= depth) {
            int s = ttScore;
            if (s >  MATE - 1000) s -= ply;
            else if (s < -MATE + 1000) s += ply;
            if (ttFlag == 1) return s;
            if (ttFlag == 3 && s >= beta)  return s;
            if (ttFlag == 2 && s <= alpha) return s;
        }
    }

    // ---- Null move pruning ----
    if (nullOk && !pvNode && !inCheck && depth >= 3 && ply > 0 && hasNonPawnMaterial()) {
        int R = 2 + depth / 6;
        makeNullMove();
        int score = -search(depth - 1 - R, -beta, -beta + 1, ply + 1, false);
        unmakeNullMove();
        if (stopSearch) return 0;
        if (score >= beta) return beta;
    }

    int origAlpha = alpha;
    MoveList ml;
    generateMoves(ml, false);
    scoreMoves(ml, ttMove, ply);

    Move bestMove;
    int  bestScore = -INF;
    int  moveCount = 0;

    for (int i = 0; i < ml.count; i++) {
        pickBest(ml, i);
        Move m = ml.moves[i];

        // Classify before makeMove: afterward mailbox[m.to] contains our piece.
        bool isQuiet = !(m.flags & FLAG_EP) && mailbox[m.to] < 0 && !m.promo;

        makeMove(m);
        if (isSquareAttacked(kingSq[side ^ 1], side)) { unmakeMove(m); continue; }
        moveCount++;

        int score;
        if (moveCount == 1) {
            score = -search(depth - 1, -beta, -alpha, ply + 1, true);
        } else {
            int reduction = 0;
            if (depth >= 3 && moveCount > 3 && isQuiet && !inCheck) {
                reduction = 1 + (moveCount > 6) + (depth > 6);
                if (pvNode) reduction--;
                reduction = max(0, reduction);
            }
            score = -search(depth - 1 - reduction, -alpha - 1, -alpha, ply + 1, true);
            if (score > alpha && reduction > 0)
                score = -search(depth - 1, -alpha - 1, -alpha, ply + 1, true);
            if (score > alpha && score < beta)
                score = -search(depth - 1, -beta, -alpha, ply + 1, true);
        }

        unmakeMove(m);
        if (stopSearch) return 0;

        if (score > bestScore) {
            bestScore = score;
            bestMove  = m;
            if (ply == 0) rootBest = m;
        }
        if (score > alpha) alpha = score;
        if (alpha >= beta) {
            if (isQuiet) {
                if (!(killers[0][ply] == m)) {
                    killers[1][ply] = killers[0][ply];
                    killers[0][ply] = m;
                }
                historyTable[m.from][m.to] += depth * depth;
                if (historyTable[m.from][m.to] > 100000)
                    historyTable[m.from][m.to] = 100000;
            }
            break;
        }
    }

    if (moveCount == 0)
        return inCheck ? (-MATE + ply) : 0;

    // ---- TT store ----
    int flag = 1;
    if (bestScore <= origAlpha) flag = 2;
    else if (bestScore >= beta) flag = 3;

    int storeScore = bestScore;
    if (storeScore >  MATE - 1000) storeScore += ply;
    else if (storeScore < -MATE + 1000) storeScore -= ply;

    // Preserve a deeper entry when a different position collides in this slot.
    if (tte.flag == 0 || tte.key == hashKey || depth >= tte.depth) {
        tte.key   = hashKey;
        tte.score = storeScore;
        tte.move  = encodeMove(bestMove);
        tte.depth = (uint8_t)min(depth, 255);
        tte.flag  = (uint8_t)flag;
    }

    return bestScore;
}

// ------------------------- Root / UCI glue -------------------------
void printScore(int score) {
    if (score > MATE - 1000)
        cout << "mate " << (MATE - score + 1) / 2;
    else if (score < -MATE + 1000)
        cout << "mate " << -((MATE + score + 1) / 2);
    else
        cout << "cp " << score;
}

void think(int maxDepth, long long timeMs) {
    stopSearch = false;
    nodes = 0;
    searchStart = chrono::steady_clock::now();
    timeLimitMs = timeMs;

    memset(killers, 0, sizeof(killers));
    memset(historyTable, 0, sizeof(historyTable));

    Move bestMove;
    for (int d = 1; d <= maxDepth; d++) {
        rootBest = Move();
        int score = search(d, -INF, INF, 0, true);
        if (stopSearch) break;

        bestMove  = rootBest;

        long long ms = elapsedMs();
        cout << "info depth " << d << " score ";
        printScore(score);
        cout << " nodes " << nodes
             << " nps " << (ms > 0 ? (long long)nodes * 1000 / ms : 0)
             << " time " << ms
             << " pv " << moveToStr(bestMove) << endl;

        if (ms > 5 && timeLimitMs > 0 && ms > timeLimitMs * 45 / 100) break;
        if (abs(score) > MATE - 1000) break;
    }

    if (bestMove.isNull()) {
        MoveList ml;
        generateMoves(ml, false);
        for (int i = 0; i < ml.count; i++)
            if (isLegal(ml.moves[i])) { bestMove = ml.moves[i]; break; }
    }
    cout << "bestmove " << moveToStr(bestMove) << endl;
}

Move parseMove(const string &s) {
    if (s.size() < 4) return Move();
    int from = (s[1] - '1') * 8 + (s[0] - 'a');
    int to   = (s[3] - '1') * 8 + (s[2] - 'a');
    int promo = 0;
    if (s.size() >= 5) {
        char c = tolower(s[4]);
        promo = (c == 'n') ? KNIGHT : (c == 'b') ? BISHOP : (c == 'r') ? ROOK : QUEEN;
    }
    MoveList ml;
    generateMoves(ml, false);
    for (int i = 0; i < ml.count; i++) {
        Move m = ml.moves[i];
        if (m.from == from && m.to == to && m.promo == promo) {
            if (isLegal(m)) return m;
        }
    }
    return Move();
}

// ------------------------- Main -------------------------
int main() {
    resizeHash(64);
    initTables();
    setFen("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");

    thread searchThread;
    string line;

    while (getline(cin, line)) {
        istringstream ss(line);
        string token;
        ss >> token;

        if (token == "uci") {
            cout << "id name Chess Bot" << endl;
            cout << "id author Chess Bot project" << endl;
            cout << "option name Hash type spin default 64 min 1 max 1024" << endl;
            cout << "uciok" << endl;
        }
        else if (token == "isready") {
            cout << "readyok" << endl;
        }
        else if (token == "setoption") {
            string nameWord, optionName, valueWord;
            ss >> nameWord >> optionName >> valueWord;
            if (nameWord == "name" && optionName == "Hash" && valueWord == "value") {
                int mb = 64;
                if (ss >> mb) {
                    if (searchThread.joinable()) {
                        stopSearch = true;
                        searchThread.join();
                    }
                    resizeHash(mb);
                }
            }
        }
        else if (token == "ucinewgame") {
            clearTT();
            setFen("rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1");
        }
        else if (token == "position") {
            string sub;
            ss >> sub;
            string fen;
            if (sub == "startpos") {
                fen = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";
                string tmp;
                ss >> tmp; // "moves"
            } else if (sub == "fen") {
                string part;
                for (int i = 0; i < 6 && (ss >> part); i++) {
                    fen += part;
                    if (i < 5) fen += " ";
                }
            }
            setFen(fen);
            string mv;
            while (ss >> mv) {
                if (mv == "moves") continue;
                Move m = parseMove(mv);
                if (m.isNull()) break;
                makeMove(m);
            }
            // rebuild history so posHistory[0] is the position start
            // (kept as is — search only cares about repetitions from here on)
        }
        else if (token == "go") {
            if (searchThread.joinable()) searchThread.join();

            int depth = MAX_PLY, movetime = 0;
            long long wtime = 0, btime = 0, winc = 0, binc = 0;
            int movestogo = 0;

            string t;
            while (ss >> t) {
                if      (t == "depth")     ss >> depth;
                else if (t == "movetime")  ss >> movetime;
                else if (t == "wtime")     ss >> wtime;
                else if (t == "btime")     ss >> btime;
                else if (t == "winc")      ss >> winc;
                else if (t == "binc")      ss >> binc;
                else if (t == "movestogo") ss >> movestogo;
                else if (t == "infinite")  movetime = 0;
            }

            long long limit = 0;
            if (movetime > 0) limit = max(1, movetime - min(30, movetime / 10));
            else {
                long long t0 = (side == WHITE) ? wtime : btime;
                long long inc = (side == WHITE) ? winc  : binc;
                if (t0 > 0) {
                    int mtg = movestogo ? movestogo : 30;
                    limit = t0 / mtg + inc * 3 / 4;
                    limit = min(limit, max(1LL, t0 - 50));
                    limit = max(1LL, limit);
                }
            }

            stopSearch = false;
            searchThread = thread([depth, limit]() { think(depth, limit); });
        }
        else if (token == "stop") {
            stopSearch = true;
            if (searchThread.joinable()) searchThread.join();
        }
        else if (token == "quit") {
            stopSearch = true;
            if (searchThread.joinable()) searchThread.join();
            break;
        }
    }

    if (searchThread.joinable()) searchThread.join();
    return 0;
}