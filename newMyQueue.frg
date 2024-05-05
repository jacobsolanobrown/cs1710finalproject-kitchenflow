#lang forge/temporal
//option min_tracelength 5

---------- Definitions ----------
sig Queue {
    //var head: lone Dish,
    var tail: lone Dish 
}

sig Dish {
    var next: lone Dish
    //var value : one Int
}


// pred myEnqueue[q: one kitchenQueue, order: one Dish] {
//     // if there is no head, then there cannot be a queue - no matter if there is a tail 
//     // if queue is empty 
//     (q.tail = none) implies {
//         (q.head' = order) and (q.tail' = order) //and (q.head.prev' = none) and (q.tail.prev' = none)
//         //we do not deal with the prev or next dishes yet 
//     }
//     // if there only one item, then make the tail the second item 
//     (some q.tail and no q.tail.next) implies {
//         (q.head' = q.head)and (q.tail' = order) and (q.tail.next' = q.head)
//     }

//     // (some q.head and some q.tail) implies {
//     //     (q.head' = q.head) and (q.tail' = q.tail)
//     // }
//     // if there is a head and a tail, then add the new item prev to the tail 
// }

// pred myenqueue[q: one Queue, order: one Dish] {
//     (q.head = none) implies  // empty queue
//         q.head' = order and e.next' = none
//     (some q.head and no q.head.next) implies { // one thing in the queue
//         q.head' = order and order.next' = q.head
//     }
//     (some q.head and some q.head.next) implies { // more than one thing in the quue and 
//         q.head' = 
//         e.next' = q.tail
//         all v: q.tail.*next | {
//             v.next' = v.next
//         }
//     }
// }

pred enqueue[q: one Queue, e: one Dish] {
    (q.tail = none) // empty queue
        => q.tail' = e and e.next' = none
    (some q.tail and no q.tail.next) => { // one thing in the queue
        q.tail' = e and e.next' = q.tail
    }
    (some q.tail and some q.tail.next) => { // more than one thing in the quue and 
        q.tail' = e
        e.next' = q.tail
        all v: q.tail.*next | {
            v.next' = v.next
        }
    }
}

pred wellformed {   
    // a dish cannot point to itself as next 
    // a dish next cannot be reflexive 
    // all order: Dish | {
    //     order.next != order
    // }

    // add if no head, then no queue
    all q: kitchenQueue | {
        // there cannot be a queue if there is not a head and a tail 
        // no q implies {
        //     no q.head and no q.tail
        // }
        // if there is a head, then the tail has to be nonempty and there cannot be anything prev to that tail 
        (q.tail = none) implies {
            q.head = none  //and (q.head.next' = none)
        }
        some q.tail implies {
            some q.head
        }

        // if there is a head, then the head has to be nonempty as well
        // (q.tail != none) implies {
        //     (q.head != none) //and (q.tail.prev' = none)
        // } 
        // (q.head != none) implies {
        //     (q.head.next = none)
        // }
    }
    // all d: Dish | {
    //     d.next != none implies {
    //         d.prev != d.next
    //     }
    //     d.prev != none implies {
    //         d.prev != d.next
    //     }
        
    // }
    // they cannot be reflexive 
    //some d: Dish | d.prev != d.next and d.next != d.prev
    // all food: Dish | food != food.next and food != food.prev 
    // all food: Dish | food not in food.^next
}

pred init[q: Queue] {
    q.tail = none 
    //q.tail = none
    // all d: Dish | {
    //     d.next = none
    // }
}


pred kitchenSetup {
    some d: Dish | {
        ///d in satCustomers.beforeOrder implies {5
            some line: Queue | {
                enqueue[line, d]
            }
        }
    //} 
}

pred welvallFormed {
    all s: Dish | {
        s not in s.^next
        s not in Queue.tail.*next => {
            no s.next
            no next.s
        }
    }
}

pred three_State{
     some e1, e2, e3: Dish, q: Queue | {
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
    welvallFormed
    three_State
}

// run {
//     some q: Queue | init[q]
//     //always wellformed
//     kitchenSetup 
// }  for 4 Dish, 1 Queue

