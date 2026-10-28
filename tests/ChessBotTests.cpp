#define main chessbot_uci_main
#include "../ChessBot.cpp"
#undef main
#include <cstdlib>

static U64 perft(int depth) {
    if (depth == 0) return 1;
    MoveList ml; generateMoves(ml, false);
    U64 total = 0;
    for (int i = 0; i < ml.count; ++i) {
        Move m = ml.moves[i];
        makeMove(m);
        if (!isSquareAttacked(kingSq[side ^ 1], side)) total += perft(depth - 1);
        unmakeMove(m);
    }
    return total;
}

static U64 recomputeHash() {
    U64 h = 0;
    for (int p = 0; p < 12; ++p) {
        U64 b = byType[p / 6][p % 6];
        while (b) { int sq = poplsb(b); h ^= zPiece[p][sq]; }
    }
    h ^= zCastle[castling];
    if (ep >= 0 && (pawnAtt[side ^ 1][ep] & byType[side][PAWN])) h ^= zEp[ep & 7];
    if (side == BLACK) h ^= zSide;
    return h;
}

static bool runPerft(const char* name, const char* fen, int depth, U64 expected) {
    setFen(fen);
    U64 got = perft(depth);
    bool ok = got == expected;
    std::cout << (ok ? "PASS " : "FAIL ") << name << " depth=" << depth
              << " expected=" << expected << " got=" << got << '\n';
    return ok;
}

static bool runHashCase(const char* name, const char* fen, const char* moveText) {
    setFen(fen);
    bool ok = hashKey == recomputeHash();
    Move m = parseMove(moveText);
    if (m.isNull()) ok = false;
    else {
        U64 before = hashKey;
        makeMove(m);
        ok = ok && hashKey == recomputeHash();
        unmakeMove(m);
        ok = ok && hashKey == before && hashKey == recomputeHash();
    }
    std::cout << (ok ? "PASS " : "FAIL ") << name << "\n";
    return ok;
}

int main() {
    initTables(); resizeHash(1);
    int failures = 0;
    failures += !runPerft("startpos d1", "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1", 1, 20);
    failures += !runPerft("startpos d2", "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1", 2, 400);
    failures += !runPerft("startpos d3", "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1", 3, 8902);
    failures += !runPerft("startpos d4", "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1", 4, 197281);
    failures += !runPerft("perft position 3 d3", "8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - - 0 1", 3, 2812);
    failures += !runPerft("perft position 4 d3", "r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq - 0 1", 3, 9467);
    failures += !runPerft("perft position 5 d2", "rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ - 1 8", 2, 1486);
    failures += !runPerft("perft position 6 d2", "r4rk1/1pp1qppp/p1np1n2/2b1p1B1/2B1P1b1/P1NP1N2/1PP1QPPP/R4RK1 w - - 0 10", 2, 2079);
    failures += !runHashCase("uncapturable en-passant target hash", "4k3/8/8/8/8/8/P7/4K3 w - e6 0 1", "a2a3");
    failures += !runHashCase("capturable en-passant target hash", "4k3/8/8/3pP3/8/8/8/4K3 w - d6 0 1", "e5d6");
    std::cout << (failures ? "FAILED " : "ALL PASSED ") << failures << " test(s) failed\n";
    return failures ? EXIT_FAILURE : EXIT_SUCCESS;
}
