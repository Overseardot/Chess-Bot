#!/usr/bin/env python3
"""UCI protocol and search-interruption regression test for Chess Bot."""
import queue
import subprocess
import sys
import threading
import time

engine = sys.argv[1] if len(sys.argv) > 1 else "./ChessBot"
proc = subprocess.Popen([engine], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                        stderr=subprocess.PIPE, text=True, bufsize=1)
lines_queue = queue.Queue()

def reader():
    for line in proc.stdout:
        lines_queue.put(line.rstrip("\n"))
    lines_queue.put(None)

threading.Thread(target=reader, daemon=True).start()

def send(command):
    proc.stdin.write(command + "\n")
    proc.stdin.flush()

def wait_for(prefix, timeout=10):
    deadline = time.monotonic() + timeout
    lines = []
    while time.monotonic() < deadline:
        try:
            line = lines_queue.get(timeout=max(0, deadline - time.monotonic()))
        except queue.Empty:
            break
        if line is None:
            break
        lines.append(line)
        if line.startswith(prefix):
            return lines
    raise AssertionError(f"Timed out waiting for {prefix!r}; received: {lines}")

try:
    send("uci")
    uci = wait_for("uciok")
    assert any(line == "id name Chess Bot" for line in uci), uci

    send("isready")
    wait_for("readyok")

    send("setoption name Hash value 1")
    send("isready")
    wait_for("readyok")

    send("position startpos")
    send("go depth 4")
    wait_for("bestmove", timeout=15)

    # A new position must interrupt an infinite search even if its worker
    # has not yet had a chance to begin executing.
    send("go infinite")
    send("position startpos moves e2e4")
    send("go depth 3")
    wait_for("bestmove", timeout=15)

    send("quit")
    proc.wait(timeout=10)
    print("UCI smoke test passed")
finally:
    if proc.poll() is None:
        proc.kill()
        proc.wait()
