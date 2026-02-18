#lang forge/froglet

abstract sig Player {}
one sig X, O extends Player {}

sig Board {
    -- board[row][col] = player who has a piece there
    board: pfunc Int -> Int -> Player
}

-- Valid row/col ranges: rows 0-5, cols 0-6
pred wellformed[b: Board] {
    all row, col: Int | {
        (row < 0 or row > 5 or col < 0 or col > 6) implies
            no b.board[row][col]
    }
}

pred starting[b: Board] {
    all row, col: Int | no b.board[row][col]
}

/** Gravity: no floating pieces */
pred gravityHolds[b: Board] {
    all row, col: Int | {
        (row > 0 and row <= 5 and col >= 0 and col <= 6) implies {
            some b.board[row][col] implies some b.board[subtract[row,1]][col]
        }
    }
}

/** X goes first */
pred Xturn[b: Board] {
    #{row, col: Int | b.board[row][col] = X}
    =
    #{row, col: Int | b.board[row][col] = O}
}

pred Oturn[b: Board] {
    #{row, col: Int | b.board[row][col] = X}
    =
    add[1, #{row, col: Int | b.board[row][col] = O}]
}

pred balanced[b: Board] {
    Xturn[b] or Oturn[b]
}

/** Four in a row horizontally */ 
pred winRow[b: Board, p: Player] {
    some row, col: Int | {
        row >= 0 and row <= 5
        col >= 0 and col <= 3
        b.board[row][col] = p
        b.board[row][add[col,1]] = p
        b.board[row][add[col,2]] = p
        b.board[row][add[col,3]] = p
    }
}

/** Four in a column vertically */
pred winCol[b: Board, p: Player] {
    some row, col: Int | {
        row >= 0 and row <= 2
        col >= 0 and col <= 6
        b.board[row][col] = p
        b.board[add[row,1]][col] = p
        b.board[add[row,2]][col] = p
        b.board[add[row,3]][col] = p
    }
}

/** Four in a diagonal */
pred winDiag[b: Board, p: Player] {
    (some row, col: Int | {
        row >= 0 and row <= 2
        col >= 0 and col <= 3
        b.board[row][col] = p
        b.board[add[row,1]][add[col,1]] = p
        b.board[add[row,2]][add[col,2]] = p
        b.board[add[row,3]][add[col,3]] = p
    })
    or
    (some row, col: Int | {
        row >= 0 and row <= 2
        col >= 3 and col <= 6
        b.board[row][col] = p
        b.board[add[row,1]][subtract[col,1]] = p
        b.board[add[row,2]][subtract[col,2]] = p
        b.board[add[row,3]][subtract[col,3]] = p
    })
}

pred winning[b: Board, p: Player] {
    winRow[b, p] or winCol[b, p] or winDiag[b, p]
}

/**
 * Drop player p's piece into column moveCol.
 * Piece lands in the lowest empty row of that column.
 */
pred move[pre: Board, moveCol: Int, p: Player, post: Board] {
    -- GUARD
    p = X implies Xturn[pre]
    p = O implies Oturn[pre]

    moveCol >= 0
    moveCol <= 6

    -- Column not full
    no pre.board[5][moveCol]

    -- Game not over
    not winning[pre, X]
    not winning[pre, O]

    -- Gravity holds in pre
    gravityHolds[pre]

    -- Find landing row: lowest empty row in moveCol
    some landingRow: Int | {
        landingRow >= 0
        landingRow <= 5
        no pre.board[landingRow][moveCol]
        (landingRow = 0 or some pre.board[subtract[landingRow,1]][moveCol])

        -- Place piece
        post.board[landingRow][moveCol] = p

        -- Frame condition
        all r, c: Int | (r != landingRow or c != moveCol) implies
            post.board[r][c] = pre.board[r][c]
    }
}

/** Find a winning board for X */
example_win: run {
    some b: Board | {
        wellformed[b]
        balanced[b]
        gravityHolds[b]
        winning[b, X]
    }
} for exactly 1 Board, 4 Int

/** Single step */
one_step: run {
    some b1, b2: Board | {
        wellformed[b1]
        balanced[b1]
        gravityHolds[b1]
        some c: Int, p: Player | move[b1, c, p, b2]
    }
} for exactly 2 Board, 4 Int

///////////////////////////////////////////////////////////
// Full game trace
///////////////////////////////////////////////////////////

one sig Game {
    first: one Board,
    next: pfunc Board -> Board
}

pred wellformed_game {

    starting[Game.first]

    all b: Board | {
        wellformed[b]
        gravityHolds[b]
        balanced[b]
    }

    all b1, b2: Board |
        Game.next[b1] = b2 implies {
            some c: Int, p: Player |
                move[b1, c, p, b2]
        }

    all b: Board |
        (winning[b, X] or winning[b, O]) implies {
            no Game.next[b]
        }

    all b: Board |
        b != Game.first implies {
            one bPrev: Board | Game.next[bPrev] = b
        }
}

a_game: run {
    wellformed_game
    some b: Board | winning[b, X]
} for 4 Int, 8 Board
