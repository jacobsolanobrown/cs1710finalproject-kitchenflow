#lang forge/temporal

---------- Definitions ----------
sig Queue {
    var head : lone Dish
}

sig Dish {
    var next : lone Dish
    ///  value just to see how its stored 
}

// enqueue a dish 
pred enqueue[q: one Queue, order: one Dish] {
    // if the queue is empty - 
    (q.head = none) implies {
        // make the head be the dish and next be nothing 
        (q.head' = order) and (order.next' = none)
    }

    // if there is a dish in the queue and nothing next 
    (some q.head and no q.head.next) implies {
        // leave the dish as head and add a node to the next node 
        (q.head' = order) and (order.next' = q.head)
    }
    // if there is a dish and next dish 
    (some q.head and some q.head.next) implies {
        // leave the head as the dish 
        (q.head' = order)
        // leave the next node as the next dish 
        order.next' = q.head
        // uniion the head with all the next ones  
        all nodes: q.head.*next | {
            nodes.next' = nodes.next
        }
    }
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
    some order: Dish | {
        order.next != order
    }
}



pred kitchenSetup {
    some d: Dish | {
        ///d in satCustomers.beforeOrder implies {5
            some kitchenQ: Queue | {
                enqueue[kitchenQ, d]
            }
        }
    //} 
}


run {
    wellformed
    kitchenSetup 
}  for 3 Dish, 1 Queue

