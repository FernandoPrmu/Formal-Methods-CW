MACHINE Battleships

SEES GlobalConstants

VARIABLES
    fleets,             /* (Player, Coordinate) |-> Ship */
    shots,              /* Player <-> Coordinate (Relation) */
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
            /* FIXED: Access shots for this player using relational image */
            report := error_overlap 
        ELSE
            /* Update shots: Union of relation and new pair */
            shots := shots \/ { player |-> (xx |-> yy) } ||
            current_turn := next_turn(player) ||
            
            /* Check Hit on Opponent */
            IF ( (next_turn(player) |-> (xx |-> yy)) : dom(fleets) ) THEN
                
                LET hit_ship BE hit_ship = fleets(next_turn(player) |-> (xx |-> yy)) IN
                   
                   /* FIXED SUNK CHECK: 
                      1. Get all fleet pairs for that ship: fleets |> {hit_ship}
                      2. Get coordinates for opponent: ... [{next_turn(player)}]
                      3. Compare with player's shots + new shot
                   */
                   IF ( 
                        dom(fleets |> {hit_ship})[{next_turn(player)}] 
                        <: 
                        (shots[{player}] \/ {(xx |-> yy)})
                   ) THEN
                        report := sunk ||
                        
                        /* FIXED WIN CHECK:
                           1. Get ALL coordinates of opponent: dom(fleets)[{next_turn(player)}]
                        */
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
                END
            ELSE
                report := miss
            END
        END
    END;

    shipSquares <-- LocationOfShips(player) =
    PRE player : PLAYER THEN
        /* FIXED: Use Relational Image to get just the coordinates for the player */
        shipSquares := dom(fleets)[{player}]
    END;

    shipsCount <-- ShipsLeft(player) =
    PRE player : PLAYER THEN
        shipsCount := card(
            { sh | sh : SHIP & 
              /* 1. Ship exists in player's fleet */
              sh : ran( ({player} * GRID) <| fleets ) &
              /* 2. Ship is NOT a subset of opponent's shots */
              not(
                  dom(fleets |> {sh})[{player}]   /* Coordinates of this ship */
                  <: 
                  shots[{next_turn(player)}]      /* Opponent's shots */
              )
            }
        )
    END;

    shotCount <-- ShotsTaken(player) =
    PRE player : PLAYER THEN
        /* FIXED: Count the size of the set of shots for this player */
        shotCount := card( shots[{player}] )
    END;

    report <-- GameState =
    BEGIN
        report := game_status
    END

END