# CSCI1710_MidtermProject

# Project Objective:
    We are modeling Connect 4. Due to the restictions of the Froglet and the most aount of moves we are able to go up are 7. fortenute for us, this is exctly how many moves are needed to have a winner and a looser. The goal of cennect 4 is in its title, the first person to put 4 tiles in a row either verticaly, horizontaly, and diagonaly wins. Unlike tic tac toe, when playing the real game gravity affects the peices, thus if a piece will go to the drop through a column until it hits the bottom row or a piece under it. 

# Model Design and Visualization:
    As stated above, our model is desinged to play a game where a winner is reached in 7 oves. that is, each player will play a piece at each baord. when looking at the Table view of the model, you can the starting board under the tab: first. When looking at the board tab, you will see this first board is not present. that is becouse, at the starting board, no piece has been played. Then, looking at the next board, found on the last column of the next table, you will see there is one pice that has been played. The next baord, then has 2 peices played, one from each player. and this alternating keeps goining until a winner is found. 

# Signatures and Predicates:
    1. abstract sig Player {} - A sig that creates a player. this is so each board can be atributed to a specific player

    2. one sig RED, YELLOW extends Player {} - This sig extends board, there are 2 players, one is yellow and one is red.

    3. sig Board - This is wat the game is bieng played on. each board, is a moment in time during the game that holds all the data about where the player have played. A connect 4 baord has the dimensions of: 6x7

    4. pred wellformed - Takes in a board, this makes sure that baord has a piece within the board dimensions

    5. pred starting - takes in a baord, and defines the baord using at the starting state, which is a board that has no pieces played within the baord at all. 

    6. pred gravityHolds - this takes in a baord and akes sure that all peices being played are "affected by gravity". this means that all boards have no flaoting peices and all peices are at the lowest position in a column

    7. pred Redturn - This takes in a board and makes sure its reds mov by ensureing that red and yellow have made the same amoutn of moves

    8. pred Yellowturn - This takes ina baord and unsures it's yellows turn by coutningup each peices, since red awlasy goes first, there should always be one more red tile played then yellow if its yellows turn. 

    9. pred balanced - Takes in a baord, and makes sure that at any given time either yellowturn or red turn is true so each player switches turns at a given time. 

    10. pred winRow - This checks to see if a player has one on a board anywhere by having 4 in a row horizontaly

    11. pred winCol - This checks to see if a player has one on a board anywhere by having 4 in a row verticaly

    12. pred winDiag - This checks to see if a player has one on a board anywhere by having 4 in a row by checking both diagonal directions. 

    13. pred winning - This pred checks to see if anyone has satisfied any of the winrow, wincol, or windiag preds at each turn. 

    14. pred move - This makes a legal move by following all the pred decribed above. It updates the board and transitions to the next baord state with the player having made a move.

    15. one sig Game - This holds the full game inside of it, it starts at the first game board, and playes out the game linearly by going to the next board. 

    16. pred wellformed_game - This combines the single-board predicates into a valid game structure; ensures every transition is legal and the game stops after a win

    17. pred linear_game- This makes sure there are no cycles in tha game and that it unfolds linearly. this makes sure no board that has been visited(played on) is played on again. 

# Testing: 



