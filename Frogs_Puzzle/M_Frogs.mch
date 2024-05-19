/* M_Frogs
 * Author: lypess
 * Creation date: 10/05/24
 */
MACHINE
    M_Frogs
    
SETS
    FROG = {male, female}
    
CONSTANTS
    NUM_FROG,
    NUM_STONES
    
PROPERTIES
    NUM_FROG = 6
    & NUM_STONES = 7    
    
VARIABLES
    frogs,
    stones
    
INVARIANT
    // frogs is a surjection between the set {1, 2, 3, ... , NUM_FROG} and FROG  
    frogs : 1..NUM_FROG --> FROG
    
    // stones is a total injective function between the set {1, 2, 3, ... , NUM_STONES} and set {0, 2, 3, ... , NUM_FROG}. Note, zero's "void" element
    & stones : 1..NUM_STONES >->> 0..NUM_FROG
    
    //Solution? For all st1 that st1 belongs {1, ... , NUM_STONES} and st1 is a stones further left and has a frog, then the frog is a female. For all st2 that st2 belongs {1, ... , NUM_STONES} and st2 is a stones further right and has a frog, then the frog is a male.
    & not(!(st1) . (st1 : 1..NUM_STONES & st1 < (NUM_STONES / 2) & stones(st1) /= 0 => frogs(stones(st1)) = female) & !(st2) . (st2 : 1..NUM_STONES & st2 > ((NUM_STONES / 2) + 1) & stones(st2) /= 0 => frogs(stones(st2)) = male))
    
INITIALISATION
    // First half I'm modeling as a male frog and the other part as a female frog
    //frogs := {1..(NUM_FROG / 2) |-> male, (NUM_FROG / 2 + 1)..NUM_FROG |-> female}   
    frogs := (1..(NUM_FROG/2)) * {male}
             \/ ((NUM_FROG/2)+1..NUM_FROG) * {female}
    
    // Initial scenarios in the first stones have just only male frogs and the last one has just female frogs 
    || stones := (1..(NUM_STONES)) * {0} 
                 <+ ({ii, jj | ii : 1..(NUM_STONES / 2) & jj = ii}
                    \/ {ii, jj | ii : ((NUM_STONES / 2) + 2)..(NUM_STONES) & jj = (ii - 1)} )


OPERATIONS
    male_jump_one(from, to) = 
    PRE
        from : dom(stones) & to : dom(stones) & from /= to & stones(from) /= 0 & stones(to) = 0 & frogs(stones(from)) = male & (to - from) = 1
    THEN
        stones := stones <+ {
            to |-> (stones(from)),
            from |-> (0)
        }
    END;
    
    male_jump_two(from, to) = 
    PRE
        from : dom(stones) & to : dom(stones) & from /= to & stones(from) /= 0 & stones(to) = 0 & frogs(stones(from)) = male & (to - from) = 2 & stones(from + 1) /= 0
    THEN
        stones := stones <+ {
            to |-> (stones(from)),
            from |-> (0)
        }
    END;
    
    //Female Jump One
    female_jump_one(from, to) = 
    PRE
        from : dom(stones) & to : dom(stones) & from /= to & stones(from) /= 0 & stones(to) = 0 & frogs(stones(from)) = female & (from - to) = 1
    THEN
        stones := stones <+ {
            to |-> (stones(from)),
            from |-> (0)
        }
    END;
    
    female_jump_two(from, to) = 
    PRE
        from : dom(stones) & to : dom(stones) & from /= to & stones(from) /= 0 & stones(to) = 0 & frogs(stones(from)) = female & (from - to) = 2 & stones(from - 1) /= 0
    THEN
        stones := stones <+ {
            to |-> (stones(from)),
            from |-> (0)
        }
    END

END
