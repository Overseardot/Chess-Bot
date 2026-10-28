#!/usr/bin/env python3
"""Run a reproducible UCI engine-vs-engine match (requires python-chess).

Example:
  python3 tests/uci_match.py --engine-a ./ChessBot --engine-b stockfish --games 10 --depth 8

This reports match results only; it does not claim an Elo estimate from a small sample.
"""
import argparse
import collections
import os
import sys
import chess
import chess.engine

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--engine-a", required=True, help="Path/name of first UCI engine")
    parser.add_argument("--engine-b", required=True, help="Path/name of second UCI engine")
    parser.add_argument("--games", type=int, default=10)
    parser.add_argument("--depth", type=int, default=8)
    parser.add_argument("--hash-mb", type=int, default=64)
    parser.add_argument("--max-plies", type=int, default=300)
    args = parser.parse_args()
    if args.games < 1 or args.depth < 1 or args.hash_mb < 1 or args.max_plies < 2:
        parser.error("games, depth, hash-mb, and max-plies must be positive")

    engines = [
        chess.engine.SimpleEngine.popen_uci(args.engine_a),
        chess.engine.SimpleEngine.popen_uci(args.engine_b),
    ]
    names = [os.path.basename(args.engine_a), os.path.basename(args.engine_b)]
    results = collections.Counter()
    try:
        for engine in engines:
            options = engine.options
            if "Hash" in options:
                engine.configure({"Hash": min(args.hash_mb, int(options["Hash"].max or args.hash_mb))})

        for game_no in range(args.games):
            # Alternate colors to reduce first-move/color bias.
            white_idx = game_no % 2
            black_idx = 1 - white_idx
            board = chess.Board()
            plies = 0
            while not board.is_game_over(claim_draw=True) and plies < args.max_plies:
                idx = white_idx if board.turn == chess.WHITE else black_idx
                result = engines[idx].play(board, chess.engine.Limit(depth=args.depth))
                if result.move is None or result.move not in board.legal_moves:
                    # A missing/illegal move is an engine failure and a loss.
                    winner_idx = 1 - idx
                    score = "1-0" if winner_idx == white_idx else "0-1"
                    print(f"Game {game_no + 1}: {score} (invalid/no move by {names[idx]})")
                    break
                board.push(result.move)
                plies += 1
            else:
                # Loop ended normally; adjudicate terminal position or ply cap.
                outcome = board.outcome(claim_draw=True)
                score = outcome.result() if outcome else "1/2-1/2"
                print(f"Game {game_no + 1}: {score} ({plies} plies)")
            if 'score' not in locals():
                outcome = board.outcome(claim_draw=True)
                score = outcome.result() if outcome else "1/2-1/2"
                print(f"Game {game_no + 1}: {score} ({plies} plies)")
            if score == "1-0":
                results[names[white_idx] + " wins"] += 1
            elif score == "0-1":
                results[names[black_idx] + " wins"] += 1
            else:
                results["draws"] += 1
            del score
    finally:
        for engine in engines:
            engine.quit()

    print("\nFinal results")
    print(f"{names[0]} wins: {results[names[0] + ' wins']}")
    print(f"{names[1]} wins: {results[names[1] + ' wins']}")
    print(f"Draws: {results['draws']}")
    print("Note: use many games and fixed time controls before drawing strength/Elo conclusions.")

if __name__ == "__main__":
    main()
