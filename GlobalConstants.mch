/* GlobalConstants
 * Author: User
 * Creation date: 1/3/2026
 */
MACHINE
    GlobalConstants
    
SETS
    /* source: 17, 18 - Two players */
    PLAYER = {player1, player2};
    
    /* source: 49-53 - Three specific ship types */
    SHIP = {submarine, destroyer, cruiser};
    
    /* Used for Deploy operations */
    ORIENTATION = {horizontal, vertical};
    
    /* source: 80, 84, 88, 92, 94, 95 - various report outputs */
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
    
    /* source: 105, 106 - Game states */
    GAME_STATE_TYPE = {setting_up, playing, player1_wins, player2_wins}

CONSTANTS
    grid_x,
    grid_y,
    GRID,
    next_turn

PROPERTIES
    /* source: 48 - Grid size 10x10 */
    grid_x = 1..10 &
    grid_y = 1..10 &
    GRID = grid_x * grid_y &
    
    /* Helper to switch turns */
    next_turn : PLAYER >-> PLAYER &
    next_turn = {player1 |-> player2, player2 |-> player1}

END
