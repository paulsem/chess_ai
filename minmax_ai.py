import chess
import math
import random
import sys
import numpy


def minimaxRoot(depth, board, isMaximizing):
    possibleMoves = board.legal_moves
    bestMove = -9999
    bestMoveFinal = None
    for x in possibleMoves:
        move = chess.Move.from_uci(str(x))
        board.push(move)
        value = max(bestMove, minimax(depth - 1, board, -10000, 10000, not isMaximizing))
        board.pop()
        if (value > bestMove):
            # print("Best score: ", str(bestMove))
            # print("Best move: ", str(bestMoveFinal))
            bestMove = value
            bestMoveFinal = move
    return bestMoveFinal


def minimax(depth, board, alpha, beta, is_maximizing):
    if (depth == 0):
        return -evaluation(board)
    possibleMoves = board.legal_moves
    if (is_maximizing):
        bestMove = -9999
        for x in possibleMoves:
            move = chess.Move.from_uci(str(x))
            board.push(move)
            bestMove = max(bestMove, minimax(depth - 1, board, alpha, beta, not is_maximizing))
            board.pop()
            alpha = max(alpha, bestMove)
            if beta <= alpha:
                return bestMove
        return bestMove
    else:
        bestMove = 9999
        for x in possibleMoves:
            move = chess.Move.from_uci(str(x))
            board.push(move)
            bestMove = min(bestMove, minimax(depth - 1, board, alpha, beta, not is_maximizing))
            board.pop()
            beta = min(beta, bestMove)
            if (beta <= alpha):
                return bestMove
        return bestMove


def calculateMove(board):
    possible_moves = board.legal_moves
    # if len(possible_moves) == 0:
    #     print("No more possible moves...Game Over")
    #     sys.exit()
    bestMove = None
    bestValue = -9999
    n = 0
    for x in possible_moves:
        move = chess.Move.from_uci(str(x))
        board.push(move)
        boardValue = -evaluation(board)
        board.pop()
        if (boardValue > bestValue):
            bestValue = boardValue
            bestMove = move

    return bestMove

PAWN_TABLE = numpy.array([
    [0, 0, 0, 0, 0, 0, 0, 0],
    [5, 10, 10, -20, -20, 10, 10, 5],
    [5, -5, -10, 0, 0, -10, -5, 5],
    [0, 0, 0, 20, 20, 0, 0, 0],
    [5, 5, 10, 25, 25, 10, 5, 5],
    [10, 10, 20, 30, 30, 20, 10, 10],
    [50, 50, 50, 50, 50, 50, 50, 50],
    [0, 0, 0, 0, 0, 0, 0, 0]
])

KNIGHT_TABLE = numpy.array([
    [-50, -40, -30, -30, -30, -30, -40, -50],
    [-40, -20, 0, 5, 5, 0, -20, -40],
    [-30, 5, 10, 15, 15, 10, 5, -30],
    [-30, 0, 15, 20, 20, 15, 0, -30],
    [-30, 5, 15, 20, 20, 15, 0, -30],
    [-30, 0, 10, 15, 15, 10, 0, -30],
    [-40, -20, 0, 0, 0, 0, -20, -40],
    [-50, -40, -30, -30, -30, -30, -40, -50]
])

BISHOP_TABLE = numpy.array([
    [-20, -10, -10, -10, -10, -10, -10, -20],
    [-10, 5, 0, 0, 0, 0, 5, -10],
    [-10, 10, 10, 10, 10, 10, 10, -10],
    [-10, 0, 10, 10, 10, 10, 0, -10],
    [-10, 5, 5, 10, 10, 5, 5, -10],
    [-10, 0, 5, 10, 10, 5, 0, -10],
    [-10, 0, 0, 0, 0, 0, 0, -10],
    [-20, -10, -10, -10, -10, -10, -10, -20]
])

ROOK_TABLE = numpy.array([
    [0, 0, 0, 5, 5, 0, 0, 0],
    [-5, 0, 0, 0, 0, 0, 0, -5],
    [-5, 0, 0, 0, 0, 0, 0, -5],
    [-5, 0, 0, 0, 0, 0, 0, -5],
    [-5, 0, 0, 0, 0, 0, 0, -5],
    [-5, 0, 0, 0, 0, 0, 0, -5],
    [5, 10, 10, 10, 10, 10, 10, 5],
    [0, 0, 0, 0, 0, 0, 0, 0]
])

QUEEN_TABLE = numpy.array([
    [-20, -10, -10, -5, -5, -10, -10, -20],
    [-10, 0, 5, 0, 0, 0, 0, -10],
    [-10, 5, 5, 5, 5, 5, 0, -10],
    [0, 0, 5, 5, 5, 5, 0, -5],
    [-5, 0, 5, 5, 5, 5, 0, -5],
    [-10, 0, 5, 5, 5, 5, 0, -10],
    [-10, 0, 0, 0, 0, 0, 0, -10],
    [-20, -10, -10, -5, -5, -10, -10, -20]
])

def evaluation2(board):
    material = get_material_score(board)

    pawns = get_piece_position_score(board, "Pp", PAWN_TABLE)
    knights = get_piece_position_score(board, "Nn", KNIGHT_TABLE)
    bishops = get_piece_position_score(board, "Bb", BISHOP_TABLE)
    rooks = get_piece_position_score(board, "Rr", ROOK_TABLE)
    queens = get_piece_position_score(board, "Qq", QUEEN_TABLE)

    return material + pawns + knights + bishops + rooks + queens

def get_piece_position_score(board, piece_type, table):
    white = 0
    black = 0
    i = 0
    x = True
    while i<63:
        try:
            x = bool(board.piece_at(i).color)
            if x:
                type = str(board.piece_at(i))
                if type in piece_type:
                    white += table[i/8][i%8]
            else:
                type = str(board.piece_at(i))
                if type in piece_type:
                    black += table[7 - (i/8)][i%8]
        except AttributeError as e:
            x = x
        i += 1
    return white - black

def get_material_score(board):
    white = 0
    black = 0
    i = 0
    x = True
    while i < 63:
        try:
            x = bool(board.piece_at(i).color)
            if x:
                white += getPieceValue(str(board.piece_at(i)))
            else:
                black += getPieceValue(str(board.piece_at(i)))
        except AttributeError as e:
            x = x
        i += 1
    return white - black

def getPieceValue2(piece):
    if (piece == None):
        return 0
    value = 0
    if piece == "P" or piece == "p":
        value = 100
    if piece == "N" or piece == "n":
        value = 320
    if piece == "B" or piece == "b":
        value = 330
    if piece == "R" or piece == "r":
        value = 500
    if piece == "Q" or piece == "q":
        value = 900
    if piece == 'K' or piece == 'k':
        value = 20000
    # value = value if (board.piece_at(place)).color else -value
    return value

def evaluation(board):
    i = 0
    evaluation = 0
    x = True
    try:
        x = bool(board.piece_at(i).color)
    except AttributeError as e:
        x = x
    while i < 63:
        i += 1
        evaluation = evaluation + (
            getPieceValue(str(board.piece_at(i))) if x else -getPieceValue(str(board.piece_at(i))))
    return evaluation


def getPieceValue(piece):
    if (piece == None):
        return 0
    value = 0
    if piece == "P" or piece == "p":
        value = 10
    if piece == "N" or piece == "n":
        value = 30
    if piece == "B" or piece == "b":
        value = 30
    if piece == "R" or piece == "r":
        value = 50
    if piece == "Q" or piece == "q":
        value = 90
    if piece == 'K' or piece == 'k':
        value = 900
    # value = value if (board.piece_at(place)).color else -value
    return value

# def main():
#     board = chess.Board()
#     n = 0
#     print(board)
#     while n < 100:
#         if n % 2 == 0:
#             move = minimaxRoot(3, board, True)
#             move = chess.Move.from_uci(str(move))
#             board.push(move)
#         else:
#             print("Computers Turn:")
#             move = minimaxRoot(3, board, True)
#             move = chess.Move.from_uci(str(move))
#             board.push(move)
#         print(board)
#         n += 1

#
# if __name__ == "__main__":
#     main()
