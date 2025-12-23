/* BattleShip
 * Author: User
 * Creation date: 12/24/2025
 */
MACHINE
    BattleShip

SETS
    PLAYERS = {RED,BLUE};
    COMANDS = {shoot,hit,miss}
    
CONSTANTS
    X,Y,Squares
    
PROPERTIES
    X = 1..10&
    Y = 1..10&
    Squares = X*Y

END
