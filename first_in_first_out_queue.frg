#lang forge/temporal
//option min_tracelength 5

---------- Definitions ----------
sig kitchenQueue {
    var head: lone Dish,
    var tail: lone Dish 
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

    // (some q.head and some q.tail) implies {
    //     (q.head' = q.head) and (q.tail' = q.tail) and (q.tail.prev' = order) and (order.prev = none)
    // }
    // if there is a head and a tail, then add the new item prev to the tail 


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
        (q.head != none) implies {
            (q.tail != none)   //and (q.head.next' = none)
        }

        // if there is a head, then the head has to be nonempty as well
        (q.tail != none) implies {
            (q.head != none) //and (q.tail.prev' = none)
        } 
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

pred init[q: kitchenQueue] {
    q.head = none 
    q.tail = none
    all d: Dish | {
        d.next = none
    }
}


pred kitchenSetup {
    some d: Dish | {
        ///d in satCustomers.beforeOrder implies {5
            some line: kitchenQueue | {
                myEnqueue[line, d]
            }
        }
    //} 
}


run {
    some q: kitchenQueue | init[q]
    always wellformed
    kitchenSetup 
}  for 6 Dish, 1 kitchenQueue

