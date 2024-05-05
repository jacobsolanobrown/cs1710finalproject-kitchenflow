#lang forge/temporal
//option min_tracelength 5

---------- Definitions ----------
sig kitchenQueue {
    var head: lone Dish,
    var tail: lone Dish, 
    totalDish: set Dish, 
}

sig Dish {
    var next: lone Dish,
    var prev: lone Dish
    ///  value just to see how its stored 
    //var value : one Int
}


pred myEnqueue[q: one kitchenQueue, order: one Dish] {
    // if there is no head, then there cannot be a queue - no matter if there is a tail 
    // if queue is empty 
    (q.head = none) implies {
        (q.head' = order) and (q.tail' = none) //and (q.head.prev' = none) and (q.tail.prev' = none)
        //we do not deal with the prev or next dishes yet 
    }
    // if there only one item, then make the tail the second item 
    (some q.head and q.tail = none) implies {
        (q.head' = q.head )and (q.tail' = order) and (q.tail.next' = q.head)
    }

    (some q.head and some q.tail) implies {
        (q.head' = q.head) and (q.tail' = q.tail) and (q.tail.prev' = order) and (order.prev = none)
    }
    // if there is a head and a tail, then add the new item prev to the tail 


}
// enqueue a dish 
pred enqueue[q: one kitchenQueue, order: one Dish] {
    // if the queue is empty 
    (q.head = none) implies {
        // make the head be the dish and next be nothing 
        (q.head' = order) and (q.tail' = order) and (order.next' = none) and (order.prev' = q.tail')
        //(q.head' = order) and (order.next' = none) and(order.prev' = none)
    }

    // // if there is a dish in the queue and nothing next 
    // (some q.head and no q.head.next and no q.head.prev) implies {
    //     // leave the dish as head and add a node to the next node 
    //     (q.head' = q.head) and (order.next' = none) and (order.prev)
    // }

    // some q.head and no q.head.next and 
    // // if there is a dish and next dish 
    // (some q.head and some q.head.next) implies {
    //     // leave the head as the dish 
    //     (q.head' = q.head) and (order.next = )
    //     // leave the next node as the next dish 
    //     order.next' = q.head
    //     // uniion the head with all the next ones  
    //     all nodes: q.head.*next | {
    //         nodes.next' = nodes.next
    //     }
    // }
}

// dequeue a dish 
// pred dequeue[q: one Queue] { 
//     // the tail is nothing (FIFO)
//     q.tail != none
//     // if there is some tail and nothing next (just one node)
//     (some q.tail and no q.tail.next) implies {
//         (q.tail' = none) and (q.tail'.next' = none)
//     }
//         // then the tail has to be nothing next and there is nothing in the next tail 
//         //=> q.tail' = none and q.tail'.next' = none
//     // if there is some tail and some next tail 
//     (some q.tail and some q.tail.next) implies {
//         q.tail' = q.tail
//         {some top: q.tail.^next | {
//             top.next = none 
//             q.tail.*next' = q.tail.*next - top
//         }
//         }
//     }

// }

pred wellformed {   
    // a dish cannot point to itself as next 
    // a dish next cannot be reflexive 

    //all dishes in the queue that are not the head or tail need to be linked 

    all order: Dish | {
         order.next != order
    }

    some disj a, b: Dish | {
        a.next = b => b.prev = a
    }

    // add if no head, then no queue
    all q: kitchenQueue | {
        // there cannot be a queue if there is not a head and a tail 
        some a, b: Dish | {
            q.head = a
            q.tail = b 
        }
        // if there is a head, then the tail has to be nonempty and there cannot be anything prev to that tail 
        (q.head != none) implies {
            (q.tail != none) //and (q.head.next' = none)
        }

        // if there is a tail, then the head has to be nonempty as well
        (q.tail != none) implies {
            (q.head != none) //and (q.tail.prev' = none)
        } 
        
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

pred init[q: kitchenQueue] {
    q.head = none 
    q.tail = none
    all d: Dish | {
        d.prev = none
        d.next = none
    }
}


pred kitchenSetup {
    some d: Dish | {
            some line: kitchenQueue | {
                myEnqueue[line, d]
            }
        } 
}


run {
    some q: kitchenQueue | init[q]
    always wellformed
    kitchenSetup 
}  for 6 Dish, 1 kitchenQueue

