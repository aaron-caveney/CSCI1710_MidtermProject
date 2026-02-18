#lang forge/froglet

abstract sig Player {}
one sig X, O extends Player {}

/** Cells are fixed indexes for a 6-row x 7-col Connect 4 board */
sig Cell {
    row: one Int,
    col: one Int
}

sig Board {
    board: pfunc Cell -> Player
}

pred wellformed {
    all c: Cell | {
        c.row >= 0
        c.row <= 5
        c.col >= 0
        c.col <= 6
    }
    all disj c1, c2: Cell | {
        (c1.row != c2.row) or (c1.col != c2.col)
    }
}
    -- Exactly one cell per (row, col) pair
    all r: Int, c: Int |
        (r >= 0 and r <= 5 and c >= 0 and c <= 6) implies
            one cell: Cell | cell.row = r and cell.col = c
}

pred starting[b: Board] {
    all c: Cell | no b.board[c]
}

/** Gravity: a cell can only be occupied if the cell below it is also occupied,
    OR it is in row 0 (the bottom row). */
pred gravityHolds[b: Board] {
    all c: Cell | {
        some b.board[c] implies {
            c.row = 0 or
            (some below: Cell | below.row = subtract[c.row, 1] and
                                below.col = c.col and
                                some b.board[below])
        }
    }
}

/** Four in a row horizontally */
pred winRow[b: Board, p: Player] {
    some disj c1, c2, c3, c4: Cell | {
        b.board[c1] = p
        b.board[c2] = p
        b.board[c3] = p
        b.board[c4] = p
        c1.row = c2.row
        c2.row = c3.row
        c3.row = c4.row
        c2.col = add[c1.col, 1]
        c3.col = add[c1.col, 2]
        c4.col = add[c1.col, 3]
    }
}

/** Four in a column vertically */
pred winCol[b: Board, p: Player] {
    some disj c1, c2, c3, c4: Cell | {
        b.board[c1] = p
        b.board[c2] = p
        b.board[c3] = p
        b.board[c4] = p
        c1.col = c2.col
        c2.col = c3.col
        c3.col = c4.col
        c2.row = add[c1.row, 1]
        c3.row = add[c1.row, 2]
        c4.row = add[c1.row, 3]
    }
}

/** Four in a diagonal (both directions) */
pred winDiag[b: Board, p: Player] {
    -- Diagonal: up-right
    (some disj c1, c2, c3, c4: Cell | {
        b.board[c1] = p
        b.board[c2] = p
        b.board[c3] = p
        b.board[c4] = p
        c2.row = add[c1.row, 1]  c2.col = add[c1.col, 1]
        c3.row = add[c1.row, 2]  c3.col = add[c1.col, 2]
        c4.row = add[c1.row, 3]  c4.col = add[c1.col, 3]
    })
    or
    -- Diagonal: up-left
    (some disj c1, c2, c3, c4: Cell | {
        b.board[c1] = p
        b.board[c2] = p
        b.board[c3] = p
        b.board[c4] = p
        c2.row = add[c1.row, 1]  c2.col = subtract[c1.col, 1]
        c3.row = add[c1.row, 2]  c3.col = subtract[c1.col, 2]
        c4.row = add[c1.row, 3]  c4.col = subtract[c1.col, 3]
    })
}

pred winning[b: Board, p: Player] {
    winRow[b, p] or winCol[b, p] or winDiag[b, p]
}

/** X goes first: X count equals O count */
pred Xturn[b: Board] {
    #{c: Cell | b.board[c] = X} = #{c: Cell | b.board[c] = O}
}

/** O's turn: X has one more piece than O */
pred Oturn[b: Board] {
    #{c: Cell | b.board[c] = X} = add[1, #{c: Cell | b.board[c] = O}]
}

pred balanced[b: Board] {
    Xturn[b] or Oturn[b]
}

/**
 * A Connect 4 move: drop player p's piece into column moveCol.
 * The piece lands in the lowest unoccupied row of that column.
 */
pred move[pre: Board, moveCol: Int, p: Player, post: Board] {
    -- GUARD
    p = X implies Xturn[pre]
    p = O implies Oturn[pre]

    -- Column must be valid
    moveCol >= 0 and moveCol <= 6

    -- The column must not be full (row 5 must be empty)
    all topCell: Cell | (topCell.row = 5 and topCell.col = moveCol) implies
        no pre.board[topCell]

    -- Nobody has won yet
    not winning[pre, X]
    not winning[pre, O]

    -- Gravity holds in pre-state
    gravityHolds[pre]

    -- ACTION: find the landing row — lowest empty cell in moveCol
    -- The piece lands on cell c where:
    --   c.col = moveCol, no pre.board[c],
    --   and either c.row = 0 or the cell below is occupied
    some landingCell: Cell | {
        landingCell.col = moveCol
        no pre.board[landingCell]
        (landingCell.row = 0 or
            (some below: Cell |
                below.row = subtract[landingCell.row, 1] and
                below.col = moveCol and
                some pre.board[below]))

        -- Place the piece at the landing cell
        post.board[landingCell] = p

        -- Frame condition: everything else is unchanged
        all c: Cell | c != landingCell implies post.board[c] = pre.board[c]
    }
}

/** Quick check: find a board where X wins */
example_win: run {
    wellformed
    some b: Board | {
        balanced[b]
        gravityHolds[b]
        winning[b, X]
    }
} for exactly 1 Board, 5 Int, exactly 42 Cell

/** Check a single step transition */
one_step: run {
    wellformed
    some b1, b2: Board | {
        balanced[b1]
        gravityHolds[b1]
        some c: Int, p: Player | move[b1, c, p, b2]
    }
} for exactly 2 Board, 5 Int, exactly 42 Cell

///////////////////////////////////////////////////////////
// Full game trace
///////////////////////////////////////////////////////////

one sig Game {
    first: one Board,
    next: pfunc Board -> Board
}

pred wellformed_game {
    starting[Game.first]
    all b1, b2: Board | b2 = Game.next[b1] implies {
        some c: Int, p: Player | move[b1, c, p, b2]
    }
    all b: Board | Game.first != Game.next[b]
}

a_game: run {
    wellformed_game
    some b: Board | winning[b, X]
} for {
    next is linear
}