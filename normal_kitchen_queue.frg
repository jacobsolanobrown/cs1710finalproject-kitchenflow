#lang forge/temporal
option min_tracelength 5


---------- Definitions ----------

abstract sig Dish {}
// menu items 
one sig Chicken, Burger, Tofu extends Dish {}

one sig Table{
    var servedDishes: set Dish
}

// Queue Data Structure
sig Kitchen {
    var placedOrder: lone Ticket // tail of the Queue
}

sig Ticket {
    var next: lone Ticket,
    foodOrder: one Dish
}

pred enqueue[q: one Kitchen, order: one Ticket] {
    // if there is no queue - the tail is empty - then make the order the tail and have no other pointer
    (q.placedOrder = none) implies { // empty queue
        q.placedOrder' = order and order.next' = none   
    }
    // if there is one node in the queue but its only the tail, then
    // set the tail as the new Ticket order (add to the bottom of queue)and point the previous tail to the front of the queue
    (some q.placedOrder and no q.placedOrder.next) implies { // one thing in the queue 
        q.placedOrder' = order and order.next' = q.placedOrder
    }
    // if there is a valid queue such that there is more than the tail and head, then 
    // set the tail as the new Ticket order (add to the bottom of queue), and point the previous tail as the next node from the new tail
    // additionally, make sure that the Ticket orders/nodes are all connected by the tail such that in the next state, the queue 
    // remains the same and is connected to the 
    // 
    (some q.placedOrder and some q.placedOrder.next) implies { // more than one thing in the queue 
        q.placedOrder' = order
        order.next' = q.placedOrder
        all links: q.placedOrder.^next | { // for all the nodes that are linked together such that their relation is transitive 
                                // node a to b and node b to c implies node a to c - all nodes linked from the placedOrder (tail) in the og state
                                // and all - TODO: if change the operation to * reflexive-transtive what does that imply ? 
            links.next' = links.next // ensure the rest of the queue does not change between states
        }
    }
}

pred dequeue[q: one Kitchen] { 
    q.placedOrder != none // the queue cannot be empty 
    // if there just the tail (no next) - one order in queue 
    (some q.placedOrder and no q.placedOrder.next) implies { 
        // the tail is none and next remains none and queue is empty 
        (q.placedOrder' = none) and (q.placedOrder'.next' = none)
    }
    // if there is a tail and there is there is a pointer to the next order/node from the tail
    // there are two orders or more than two orders in the queue 
    (some q.placedOrder and some q.placedOrder.next) implies {
        // the tail will remain the same in FIFO queue implementation
        q.placedOrder' = q.placedOrder
        // there exists some node in the linked/reachable nodes from the queue tail such that.. 
        {some head: q.placedOrder.^next | {
            // the head next pointer is none (is the head)
            head.next = none 
            // and we remove that head node from the queue such that we only keep the other reachable nodes
            // in the next state 
            q.placedOrder.^next' = q.placedOrder.^next - head // * operation better? 
        }
        }
    } 
}

pred wellformed {   
    // for all the Tickets
    all order: Ticket | {
        // the same order cannot be linked to itself - cannot be transitive 
        order not in order.^next
        // if the order is not linked in the queue... yet :0
        // then there cannot be an pointer to the next order or a next order node - until its in the queue 
        (order not in Kitchen.placedOrder.^next) implies {
            no order.next 
            no next.order
        }
    }
}

// the initial state of the kitchen is empty with no orders yet 
pred init[q: Kitchen] {
    q.placedOrder = none // no queue 
    next = none->none  // there is no next yet 
}

// model without needing to specify/control the next pointer for each state - TODO: how to constrain the next pointer enough without needing to properly specify d2->d1?
pred kitchenSetup[q: Kitchen] {
    init[q]
    some d1, d2, d3: Ticket | {
        enqueue[q, d1]
        next_state enqueue[q, d2]
        next_state next_state enqueue[q, d3]
    }
}

pred kitchenFourOrders{
     some order1, order2, order3, order4: Ticket, q: Kitchen | {
            #(order1 + order2 + order3 + order4) = 4
            // State 0 - empty kitchen
            init[q]

            // State 1 - 1st order in!
            q.placedOrder' = order1 // just the tail of queue - 1st order in!
            next' = none->none // no next node yet since only one node in queue

            // State 2 - 2nd order in!
            q.placedOrder'' = order2 // new Ticket is added to the tail of the queue - 2nd order in!
            next'' = order2->order1 // previous tail becomes head/next 

            // State 3 - 3rd order in!
            q.placedOrder''' = order3
            next''' = order3->order2 + order2->order1

            // State 4 - 4th order in!
            q.placedOrder'''' = order4
            next'''' = order4->order3 + order3->order2 + order2->order1

            // make sure that it follows our enqueue model 
            enqueue[q, order1]
            next_state enqueue[q, order2]
            next_state next_state enqueue[q, order3]
            next_state next_state next_state enqueue[q, order4]
        }
}

pred serveOrder {
         some order1, order2: Ticket, q: Kitchen, t: Table | {
            #(order1 + order2) = 2
            // State 0 - nothing in kitchen
            init[q]
            Table.servedDishes = none


            // State 1 - 1st order in!
            q.placedOrder' = order1 // just the tail of queue - 1st order in!
            next' = none->none // no next node yet since only one node in queue
            Table.servedDishes' = Table.servedDishes


            // State 2 - 2nd order in!
            q.placedOrder'' = order2 // new Ticket is added to the tail of the queue - 2nd order in!
            next'' = order2->order1 // previous tail becomes head/next 
            Table.servedDishes'' = Table.servedDishes'


            // State 3 - 1st order out!
            q.placedOrder''' = order2
            next''' = none->none
            Table.servedDishes''' = Table.servedDishes'' + order1.foodOrder

            // State 4 - 2nd order out!
            init[q]
            Table.servedDishes'''' = Table.servedDishes''' + order2.foodOrder

            // make sure that it follows our enqueue and dequeue model 
            enqueue[q, order1]
            next_state enqueue[q, order2]
            next_state next_state dequeue[q]
            next_state next_state next_state dequeue[q]
        }
}

-- enqueuing/placing orders example 
// run {
//     wellformed
//     kitchenFourOrders
// } for 4 Ticket, 1 Kitchen

-- enqueing + dequeuing/serving orders example 
run {
    wellformed
    serveOrder
} for 2 Ticket, 1 Kitchen

-- unsat when always wellformed - cant constrain the next pointer 
// run {
//     some q: Kitchen | {
//         wellformed
//         kitchenSetup[q]
//     }
// }  for 3 Ticket, 1 Kitchen