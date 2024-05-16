/* Hanoi
 * Author: lypess
 * Creation date: 23/04/24
 */
MACHINE
    Hanoi
    
VARIABLES
    hanoi
    
INVARIANT
    // Conjunto das partes
    hanoi : 1..3 --> POW(1..3) &
    
    //Discos nao se repetem
    !(p1, p2) . ((p1 : dom(hanoi) & p2 : dom(hanoi) & p1 /= p2 => hanoi(p1) /\ hanoi(p2) = {})) 
    
    // Solucao
     & not(hanoi(1) = {} & hanoi(2) = {} & hanoi(3) = {1,2,3})

INITIALISATION
    hanoi := {1 |-> {1,2,3}, 2 |-> {}, 3 |-> {}}
OPERATIONS
    move(from, to) =
        PRE
            from : dom(hanoi) & to : dom(hanoi) & from /= to
            & hanoi(from) /= {}
            & (hanoi(to) /= {} => min(hanoi(from)) < min(hanoi(to)))
        THEN
            hanoi := hanoi <+ 
                {
                    from |-> (hanoi(from) - {min(hanoi(from))}),
                    to |-> (hanoi(to) \/ {min(hanoi(from))})
                }
        END
END
