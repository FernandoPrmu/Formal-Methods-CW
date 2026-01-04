/* GlobalConstants
 * Author: User
 * Creation date: 1/3/2026
 */
MACHINE
    GlobalConstants
    
SETS
    
    PLAYER = {player1, player2};
    
   
    SHIP = {submarine, destroyer, cruiser};
    
    
    ORIENTATION = {horizontal, vertical};
    
    
    REPORT = {
        global_ok, 
        hit, 
        miss, 
        sunk, 
        error_overlap, 
        error_out_of_bounds, 
        error_ship_already_placed, 
        error_wrong_deployment_order, 
        error_game_not_ready,
        error_not_your_turn,
        error_game_over
    };
    
   
    GAME_STATE_TYPE = {setting_up, playing, player1_wins, player2_wins}

CONSTANTS
    grid_x,
    grid_y,
    GRID,
    next_turn

PROPERTIES
    
    grid_x = 1..10 &
    grid_y = 1..10 &
    GRID = grid_x * grid_y &
    next_turn : PLAYER >-> PLAYER &
    next_turn = {player1 |-> player2, player2 |-> player1}

END
