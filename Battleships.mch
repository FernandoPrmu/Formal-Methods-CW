MACHINE Battleships

SEES GlobalConstants

VARIABLES
    fleets,             // Maps (Player |-> Coordinate) to the type of SHIP present 
    shots,              // Relation tracking which squares a PLAYER has fired upon 
    deploy_state,       // Tracks the number of ships deployed (0 to 3) per player 
    current_turn,       // Tracks whose turn it is to fire (Player 1 or Player 2) 
    game_status         // Current phase of the game: setting_up, playing, or finished 

INVARIANT
    fleets : (PLAYER * GRID) +-> SHIP &
    shots : PLAYER <-> GRID &
    deploy_state : PLAYER --> 0..3 &
    current_turn : PLAYER &
    game_status : GAME_STATE_TYPE

INITIALISATION
    // At start, the board is empty and no shots have been fired 
    fleets := {} ||
    shots := {} ||
    // Both players begin with zero ships deployed 
    deploy_state := {(player1 |-> 0), (player2 |-> 0)} ||
    // Per requirements, Player 1 always takes the first turn to shoot
    current_turn := player1 ||
    // The game begins in the setup phase 
    game_status := setting_up

OPERATIONS

    // Operation: DeploySubMarine Rule: Players must place the submarine (1x1) first.
    
    report <-- DeploySubMarine(player, xx, yy) =
    PRE
        player : PLAYER & xx : grid_x & yy : grid_y & game_status = setting_up
    THEN
        IF (game_status /= setting_up) THEN
            report := error_game_not_ready
        ELSIF (deploy_state(player) /= 0) THEN
            // Ensures submarines are placed before other ship types
            report := error_wrong_deployment_order
        ELSIF ( (player |-> (xx |-> yy)) : dom(fleets) ) THEN
            // Check if the square is already occupied by another ship 
            report := error_overlap
        ELSE
            // Add the submarine to the fleet and increment deployment counter 
            fleets := fleets \/ { (player |-> (xx |-> yy)) |-> submarine } ||
            deploy_state(player) := 1 ||
            report := global_ok
        END
    END;

    //Operation: DeployDestroyer Rule: Placed second. Occupies 2 squares.
    report <-- DeployDestroyer(player, xx, yy, orient) =
    PRE
        player : PLAYER & xx : grid_x & yy : grid_y & orient : ORIENTATION & game_status = setting_up
    THEN
        IF (game_status /= setting_up) THEN
            report := error_game_not_ready
        ELSIF (deploy_state(player) /= 1) THEN
            //Must place Submarine before Destroyer 
            report := error_wrong_deployment_order
        ELSE
            IF (orient = horizontal) THEN
                //Check if the 1x2 ship exceeds the right grid boundary 
                IF (xx + 1 > 10) THEN
                    report := error_out_of_bounds
                //Check for overlaps across both squares
                ELSIF ( {(player|->(xx|->yy)), (player|->(xx+1|->yy))} /\ dom(fleets) /= {} ) THEN
                    report := error_overlap
                ELSE
                    fleets := fleets \/ { 
                        (player|->(xx|->yy))   |-> destroyer, 
                        (player|->(xx+1|->yy)) |-> destroyer 
                    } ||
                    deploy_state(player) := 2 ||
                    report := global_ok
                END
            ELSE 
                //Logic for vertical placement (checks bottom boundary) 
                IF (yy + 1 > 10) THEN
                    report := error_out_of_bounds
                ELSIF ( {(player|->(xx|->yy)), (player|->(xx|->yy+1))} /\ dom(fleets) /= {} ) THEN
                    report := error_overlap
                ELSE
                    fleets := fleets \/ { 
                        (player|->(xx|->yy))   |-> destroyer, 
                        (player|->(xx|->yy+1)) |-> destroyer 
                    } ||
                    deploy_state(player) := 2 ||
                    report := global_ok
                END
            END
        END
    END;

    // Operation: DeployCruiser Rule: Placed last. Occupies 3 squares. Triggers the 'playing' state if both are ready.
   
    report <-- DeployCruiser(player, xx, yy, orient) =
    PRE
        player : PLAYER & xx : grid_x & yy : grid_y & orient : ORIENTATION & game_status = setting_up
    THEN
        IF (game_status /= setting_up) THEN
            report := error_game_not_ready
        ELSIF (deploy_state(player) /= 2) THEN
            //Must place Destroyer before Cruiser
            report := error_wrong_deployment_order
        ELSE
            IF (orient = horizontal) THEN
                //Check boundary and overlaps for a 1x3 ship
                IF (xx + 2 > 10) THEN
                    report := error_out_of_bounds
                ELSIF ( {(player|->(xx|->yy)), (player|->(xx+1|->yy)), (player|->(xx+2|->yy))} /\ dom(fleets) /= {} ) THEN
                    report := error_overlap
                ELSE
                    fleets := fleets \/ { 
                        (player|->(xx|->yy))   |-> cruiser, 
                        (player|->(xx+1|->yy)) |-> cruiser, 
                        (player|->(xx+2|->yy)) |-> cruiser 
                    } ||
                    deploy_state(player) := 3 ||
                    //If the opponent has also finished deployment, game starts 
                    IF (deploy_state(next_turn(player)) = 3) THEN
                        game_status := playing
                    END ||
                    report := global_ok
                END
            ELSE 
                //Vertical cruiser placement logic 
                IF (yy + 2 > 10) THEN
                    report := error_out_of_bounds
                ELSIF ( {(player|->(xx|->yy)), (player|->(xx|->yy+1)), (player|->(xx|->yy+2))} /\ dom(fleets) /= {} ) THEN
                    report := error_overlap
                ELSE
                    fleets := fleets \/ { 
                        (player|->(xx|->yy))   |-> cruiser, 
                        (player|->(xx|->yy+1)) |-> cruiser, 
                        (player|->(xx|->yy+2)) |-> cruiser 
                    } ||
                    deploy_state(player) := 3 ||
                    IF (deploy_state(next_turn(player)) = 3) THEN
                        game_status := playing
                    END ||
                    report := global_ok
                END
            END
        END
    END;

    // Operation: Shoot Logic: Handles hit/miss detection, ship sinking, and victory conditions.
    
    report <-- Shoot(player, xx, yy) =
    PRE
        player : PLAYER & xx : grid_x & yy : grid_y & game_status = playing
    THEN
        IF (game_status /= playing) THEN
            report := error_game_not_ready
        ELSIF (player /= current_turn) THEN
            report := error_not_your_turn
        ELSIF ( (xx |-> yy) : shots[{player}] ) THEN 
            //Prevent players from shooting the same coordinate twice
            report := error_overlap 
        ELSE
            //Record the shot and toggle the turn to the next player
            shots := shots \/ { player |-> (xx |-> yy) } ||
            current_turn := next_turn(player) ||
            
            //Check if the shot hits an opponent's ship
            IF ( (next_turn(player) |-> (xx |-> yy)) : dom(fleets) ) THEN
                //Sink Logic: If all squares of the specific ship hit are now in the player's shot history, the ship is 'sunk'.
                
                IF ( 
                    dom( fleets |> { fleets(next_turn(player) |-> (xx |-> yy)) } )[{next_turn(player)}] 
                    <: 
                    (shots[{player}] \/ {(xx |-> yy)})
                ) THEN
                    report := sunk ||
                    // Win Logic: If the total set of opponent's ship squares is contained within the player's shot set, the game is won.
                    IF ( 
                        dom(fleets)[{next_turn(player)}]
                        <: 
                        (shots[{player}] \/ {(xx |-> yy)})
                    ) THEN
                        IF (player = player1) THEN game_status := player1_wins
                        ELSE game_status := player2_wins END
                    END
                ELSE
                    report := hit
                END
            ELSE
                report := miss
            END
        END
    END;

    //Returns the set of all coordinates occupied by a specific player's ships 
    shipSquares <-- LocationOfShips(player) =
    PRE player : PLAYER THEN
         shipSquares := dom(fleets)[{player}]
    END;

    //Calculates how many distinct ship types have NOT been fully sunk yet 
    shipsCount <-- ShipsLeft(player) =
    PRE player : PLAYER THEN
        shipsCount := card(
            { sh | sh : SHIP & 
              sh : ran( ({player} * GRID) <| fleets ) &
              //A ship remains if at least one of its squares has not been shot by the opponent 
              not(
                  dom(fleets |> {sh})[{player}]   
                  <: 
                  shots[{next_turn(player)}]      
              )
            }
        )
    END;

    //Returns the total number of attempts fired by a player 
    shotCount <-- ShotsTaken(player) =
    PRE player : PLAYER THEN
        shotCount := card( shots[{player}] )
    END;

    //Provides the current phase or outcome of the game 
    report <-- GameState =
    BEGIN
        report := game_status
    END

END