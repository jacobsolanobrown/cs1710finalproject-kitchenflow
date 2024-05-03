#lang forge 

option problem_type temporal 

---------- Definitions ----------
sig Queue {
    var tail : lone Vehicle
}

sig Vehicle {
    var next : lone Vehicle
}

pred enqueue[q: one Queue, e: one Vehicle] {
    (q.tail = none)
        => q.tail' = e and e.next' = none
    (some q.tail and no q.tail.next) => {
        q.tail' = e and e.next' = q.tail
    }
    (some q.tail and some q.tail.next) => {
        q.tail' = e
        e.next' = q.tail
        all v: q.tail.*next | {
            v.next' = v.next
        }
    }
}

pred dequeue[q: one Queue] { 
    q.tail != none
    (some q.tail and no q.tail.next) 
        => q.tail' = none and q.tail'.next' = none
    (some q.tail and some q.tail.next) => 
        q.tail' = q.tail
        {some top: q.tail.^next | {
            top.next = none 
            q.tail.*next' = q.tail.*next - top
        }
        }
}

--------------- Verifications ----------------

pred welvallFormed {
    all s: Vehicle | {
        s not in s.^next
        s not in Queue.tail.*next => {
            no s.next
            no next.s
        }
    }
}

pred three_State{
     some e1, e2, e3: Vehicle, q: Queue | {
            #(e1 + e2 + e3) = 3

            -- State 0
            q.tail = none
            next = none->none

            -- State 1
            q.tail' = e1
            next' = none->none

            // -- State 2
            q.tail'' = e2
            next'' = e2->e1

            // -- State 3
            q.tail''' = e3
            next''' = e3->e2 + e2->e1

            -- Checking predicates
            enqueue[q, e1]
            next_state enqueue[q, e2]
            next_state next_state enqueue[q, e3]
        }
}

run {
    three_State
}

test expect {
    basicAddTest: {
        some e1, e2, e3: Vehicle, q: Queue | {
            #(e1 + e2 + e3) = 3

            -- State 0
            q.tail = none
            next = none->none

            -- State 1
            q.tail' = e1
            next' = none->none

            // -- State 2
            q.tail'' = e2
            next'' = e2->e1

            // -- State 3
            q.tail''' = e3
            next''' = e3->e2 + e2->e1

            -- Checking predicates
            enqueue[q, e1]
            next_state enqueue[q, e2]
            next_state next_state enqueue[q, e3]
        }
    } is sat

    basicRemoveTest: {
        some e1, e2, e3: Vehicle, q: Queue | {
            #(e1 + e2 + e3) = 3

            -- State 0
            q.tail = e1
            next = e1->e2 + e2->e3

            -- State 1
            q.tail' = e1
            next' = e1->e2

            // -- State 2
            q.tail'' = e1
            next'' = none->none

            -- Checking predicates
            dequeue[q]
            next_state dequeue[q]
        }
    } is sat

    basicTraceTest: {
        some e1, e2, e3: Vehicle, q: Queue | {
            #(e1 + e2 + e3) = 3

            -- State 0
            q.tail = none
            next = none->none

            -- State 1
            q.tail' = e1
            next' = none->none

            -- State 2
            q.tail'' = e2
            next'' = e2->e1

            -- State 3
            q.tail''' = e2
            next''' = none->none

            -- State 4
            q.tail'''' = e3
            next'''' = e3->e2

            -- Checking predicates
            enqueue[q, e1]
            next_state enqueue[q, e2]
            next_state next_state dequeue[q]
            next_state next_state next_state enqueue[q, e3]
        }
    } is sat
}

// example onlyTail is wellFormed for {
//     -- We can have a queue with just one element: the tail
//     Queue = `Queue0
//     Vehicle = `V0 + `V1 + `V2 + `V3
//     tail = `Queue0->`V0
// }

// example simpleLoop is not wellFormed for {
//     -- It should be impossible to reach the tail again
//     Queue = `Queue0
//     Vehicle = `V0 + `V1
//     tail = `Queue0->`V0
//     next = `V0->`V1 + `V1->`V0
// }

// example noRepeatingCars is not wellFormed for {
//     -- Cars should only show up once in the queue
//     Queue = `Queue0
//     Vehicle = `V0 + `V1 + `V2 + `V3
//     tail = `Queue0->`V0
//     next = `V0->`V1 + `V1->`V2 + `V2->`V3 + `V3->`V1
// }

// example notConnectedToQueue is not wellFormed for {
//     -- V2 is connected to V3 but is neither are reachable from the tail
//     Queue = `Queue0
//     Vehicle = `V0 + `V1 + `V2 + `V3
//     tail = `Queue0->`V0
//     next = `V0->`V1 + `V2->`V3 
// }