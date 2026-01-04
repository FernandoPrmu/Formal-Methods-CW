MACHINE Battleships

SEES GlobalConstants

VARIABLES
    fleets,             
    shots,              
    deploy_state,
    current_turn,
    game_status

INVARIANT
    fleets : (PLAYER * GRID) +-> SHIP &
    shots : PLAYER <-> GRID &
    deploy_state : PLAYER --> 0..3 &
    current_turn : PLAYER &
    game_status : GAME_STATE_TYPE

INITIALISATION
    fleets := {} ||
    shots := {} ||
    deploy_state := {(player1 |-> 0), (player2 |-> 0)} ||
    current_turn := player1 ||
    game_status := setting_up

OPERATIONS

    report <-- DeploySubMarine(player, xx, yy) =
    PRE
        player : PLAYER & xx : grid_x & yy : grid_y
    THEN
        IF (game_status /= setting_up) THEN
            report := error_game_not_ready
        ELSIF (deploy_state(player) /= 0) THEN
            report := error_wrong_deployment_order
        ELSIF ( (player |-> (xx |-> yy)) : dom(fleets) ) THEN
            report := error_overlap
        ELSE
            fleets := fleets \/ { (player |-> (xx |-> yy)) |-> submarine } ||
            deploy_state(player) := 1 ||
            report := global_ok
        END
    END;

    report <-- DeployDestroyer(player, xx, yy, orient) =
    PRE
        player : PLAYER & xx : grid_x & yy : grid_y & orient : ORIENTATION
    THEN
        IF (game_status /= setting_up) THEN
            report := error_game_not_ready
        ELSIF (deploy_state(player) /= 1) THEN
            report := error_wrong_deployment_order
        ELSE
            IF (orient = horizontal) THEN
                IF (xx + 1 > 10) THEN
                    report := error_out_of_bounds
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

    report <-- DeployCruiser(player, xx, yy, orient) =
    PRE
        player : PLAYER & xx : grid_x & yy : grid_y & orient : ORIENTATION
    THEN
        IF (game_status /= setting_up) THEN
            report := error_game_not_ready
        ELSIF (deploy_state(player) /= 2) THEN
            report := error_wrong_deployment_order
        ELSE
            IF (orient = horizontal) THEN
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
                    IF (deploy_state(next_turn(player)) = 3) THEN
                        game_status := playing
                    END ||
                    report := global_ok
                END
            ELSE 
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

    report <-- Shoot(player, xx, yy) =
    PRE
        player : PLAYER & xx : grid_x & yy : grid_y
    THEN
        IF (game_status /= playing) THEN
            report := error_game_not_ready
        ELSIF (player /= current_turn) THEN
            report := error_not_your_turn
        ELSIF ( (xx |-> yy) : shots[{player}] ) THEN 
            report := error_overlap 
        ELSE
            
            shots := shots \/ { player |-> (xx |-> yy) } ||
            current_turn := next_turn(player) ||
            IF ( (next_turn(player) |-> (xx |-> yy)) : dom(fleets) ) THEN
                IF ( 
                    dom( fleets |> { fleets(next_turn(player) |-> (xx |-> yy)) } )[{next_turn(player)}] 
                    <: 
                    (shots[{player}] \/ {(xx |-> yy)})
                ) THEN
                    report := sunk ||
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

    shipSquares <-- LocationOfShips(player) =
    PRE player : PLAYER THEN
         shipSquares := dom(fleets)[{player}]
    END;

    shipsCount <-- ShipsLeft(player) =
    PRE player : PLAYER THEN
        shipsCount := card(
            { sh | sh : SHIP & 
              sh : ran( ({player} * GRID) <| fleets ) &
              
              not(
                  dom(fleets |> {sh})[{player}]   
                  <: 
                  shots[{next_turn(player)}]      
              )
            }
        )
    END;

    shotCount <-- ShotsTaken(player) =
    PRE player : PLAYER THEN
        
        shotCount := card( shots[{player}] )
    END;

    report <-- GameState =
    BEGIN
        report := game_status
    END

END