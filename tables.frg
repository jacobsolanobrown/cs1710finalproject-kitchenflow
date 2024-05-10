#lang forge

open "normal_kitchen_queue.frg"

option problem_type temporal 

//TODO: take out customersAtTable field

//default trace length is 5 -- could enforce a new max thats a bigger number 
//use var to make state variable

------------- DEFINITIONS -------------
-------- Employees & Customers --------

abstract sig Person {}

sig Customer extends Person {
  var status: one CustomerStatus
}

abstract sig CustomerStatus {}
one sig Waiting, Seated, Ordered, Ready4Check extends CustomerStatus {} //state changes

sig Party {
  people: set Customer,
  size: one Int, 
  var spot: lone Table
}

sig Server extends Person {
  myTables: set Table
}

---------------- Table ----------------

sig Table {
  customersAtTable: set Customer, //take this out 
  tableNumber: one Int,
  capacity: one Int,
  orders: set Dish
  // price: lone Int
}

abstract sig TableStatus {
  var tables: set Table
}
one sig Available, Full extends TableStatus {} 

---------------- Dish ----------------
///?? KEEP IN HERE OR IN QUEUE 

// abstract sig Dish {
//    price: one Int
// }
// sig Burger extends Dish {}
// sig Salad extends Dish {}
// sig ChickTenders extends Dish {}

/*
--------------- VALID STATE --------------
Ensures that each state is valid - no crazy instances
--> Tables are either Available OR Full | can't be both
--> Customers are either Waiting or Seated or Ordered or Ready4Check | can't be in more than one 
--> Table numbers must be positive/in a specific range [1-5]
--> Each Table should have a unique table number
--> ?? need to state how many people are in the resturant 
*/

pred valid_state {
  --> Tables are either full or occupied, cannot be both
  Table = Available.tables + Full.tables
  no t : Table | {t in Available.tables and t in Full.tables}

 --> Tables numbers cannot be negative / need to be in a specific range (1-5)
 all t: Table | t.tableNumber > 0 and t.tableNumber < 6
 all t: Table | {#{t}<6}

 --> Each table has a unique table #
  all disj t1, t2: Table | {
    //assign unique table number 
    //TODO: limit table number scope?
    t1.tableNumber != t2.tableNumber // I think this is better 
  }
} 

/*
--------------- INIT STATES --------------
The following preds work together to Initialize Resturant at the beginning of the day | Opening State 
-- TABLE INIT
-- CUSTOMER INIT 
-- PARTY INIT 
-- SERVER INIT
-- TODO: KITCHEN INIT
*/

--------------- init tables --------------
--> All Tables are available
--> No customers at any table
--> No orders at the table
--> Setting capacity to specified range {2, 4}

pred table_init {
  Table = Available.tables

  all t: Table | {
    no c : Customer | c in t.customersAtTable
    t.orders = none
  }

  all t: Table | {
    t.capacity = 2 or t.capacity = 4
    #{c: Customer | c in t.customersAtTable} = 0 //duplicate?
  }
}

--------------- init customers --------------
--> All Customers are Waiting (none are in the resturant yet)
--> each customer is part of ONE party 

pred customer_init {
  all c: Customer | c.status = Waiting

  all c: Customer | some p: Party | {c in p.people}
}

--------------- init party --------------
--> each party has 1 or more people & the party size = the size of the customer list
--> no customer can be in two partys

pred party_init {
  all p: Party | {
    p.size > 0
    #{p.people} = {p.size}
    p.spot = none
  }

  all disj p, q: Party | {
    all c: Customer | {
      c in p.people => c not in q.people
    }
  }
}

--------------- init servers --------------
--> There are not more servers than tables in resturant
--> Each table only has one server

pred server_init {
  valid_state implies {
    all s: Server, t: Table | {
      #{s} <= #{t}
    }
  }
  
  all disj s1, s2: Server | {
    s1.myTables != s2.myTables
    no t: Table | t in s1.myTables and t in s2.myTables // this might be better 
  }
}

----------- CUSTOMER TRANSITIONS ----------
------------------- seat ------------------
--> assigns a customer party, p, to a table in resturant 

pred seat[p: Party] {
  -- GAURD
  --> Party does not have a spot
  p.spot = none 

  -- ACTION[s]
  --> trantision customers state in party, p, to seated 
  --> assings some table, t, to the parties spot field 
  --> Marks table as Full
  all c: Customer | { 
    {c in p.people => {
       c.status = Waiting => c.status' = Seated 
    } else {
      c.status = Waiting => c.status' = Waiting
    } } 
  }

  some t: Table | {
    (t in Available.tables and t.capacity >= p.size) => 
    {
      p.spot' = t
      Available.tables' = Available.tables - t
      Full.tables' = Full.tables + t
    } 
  }
}

------------------- order ------------------
--> takes party, p's, order and sends it into kitchen queue

pred order[p: Party] {
  -- GAURD
  --> no orders | table is full
  no p.spot.orders and p.spot in Full.tables

  -- CONSTANTS
  --> table spots should not change
  --> available and full tables 
  p.spot' = p.spot
  Available.tables' = Available.tables
  Full.tables' = Full.tables

  -- ACTION
  --> transition customers in table to orderd 
  --> collect customers orders and sends to kitchen
  all c: Customer | {
      c in p.people => {
        c.status = Seated => c.status' = Ordered
      } else {
        c.status' = c.status
      }
    }

  orderTicket[p]

  //TODO: collect customers orders and sends to kitchen
}

pred orderTicket[p: Party] {
  some order: Ticket | {
    // #(order1 + order2) = 2
    // State 0 - nothing in kitchen
    init[Kitchen]
    p.spot.orders = none

    // State 1 - 1st order in!
    Kitchen.placedOrder' = order // just the tail of queue - 1st order in!
    next' = none->none // no next node yet since only one node in queue
   // p.spot.orders' = p.spot.orders

    // State 3 - 1st order out!
    // q.placedOrder'' = none
    // next''' = none->none
    // p.spot.orders'' = p.spot.orders'' + order.foodOrder

    // make sure that it follows our enqueue and dequeue model 
    enqueue[Kitchen, order]
    // next_state dequeue[q]
  }
}



------------------- eating ------------------
--> ??

pred eating[p: Party] {
  -- GAURD
  -- orders are through kitchen queue 
  -- TODO: figure out w/Jacobs code      

  -- CONSTANTS
  --> table spots should not change
  p.spot' = p.spot
  --> available and full tables 
  Available.tables' = Available.tables
  Full.tables' = Full.tables

  -- ACTION
  all c: Customer | {
    c in p.people => {
        c.status = Ordered => c.status' = Ready4Check
    } else 
      c.status = c.status'
  }
  serveTicket[p]
}

pred serveTicket[p: Party] {
  some order: Ticket | {

    // State 3 - 1st order out!

    Kitchen.placedOrder = none
    next = none->none
    p.spot.orders = p.spot.orders + order.foodOrder

    // make sure that it follows our enqueue and dequeue model 
    dequeue[Kitchen]
    // next_state dequeue[q]
  }
}

------------------- leave ------------------
--> represents customers leaving the resturant, resets all fields 

pred leave[p: Party] {
  -- GARD 
  -- TODO: custoemrs done eating ??? do we need one idk 

  --> ACTION
  --> reset customer status to waiting
  --> restet party spot to none 
  --> mark table as Available 

  all c: Customer | {
    c in p.people => {
      c.status = Ready4Check => c.status' = Waiting 
    } else {
      c.status = Ready4Check => c.status' = Ready4Check 
    }
  }

  p.spot' = none 
  Available.tables' = Available.tables + p.spot
  Full.tables' = Full.tables - p.spot
}

------------------- customerTransistion ------------------
--> Transitions customers through CustomerStatus with their assigned party - does not control any other fields 

pred customerTransistion[p: Party] {  
  all c: Customer | {
    c in p.people => {
       c.status = Waiting => c.status' = Seated 
       c.status = Seated => c.status' = Ordered
       c.status = Ordered => c.status' = Ready4Check
        c.status = Ready4Check => c.status' = Waiting 
    } else {
      c.status = Waiting => c.status' = Waiting
      c.status = Seated => c.status' = Seated
      c.status = Ordered => c.status' = Ordered
      c.status = Ready4Check => c.status' = Ready4Check 
    }
  }
}

///?? KEEP IN HERE OR IN QUEUE 
// minimum that each table orders just one order of either a burger, salads, or chicktenders
pred dishOrders {
  all t: Table | {
    all food: Dish | {
      food in t.orders implies {
        food = Burger or 
        food = Salad or 
        food = ChickTenders
      }
    }
  }
}

--> cycles customers through resturant
pred run_states[p: Party] {
  some c: Customer | {
    c in p.people 
    c.status = Waiting => seat[p]
    c.status = Seated => order[p]
    c.status = Ordered => eating[p]
    c.status = Ready4Check => leave[p]
  }
} 
------------------- CHECKS ------------------
pred all_parties_seated{
  all p: Party {
    p.spot != none
  }
}

--------------- RUN STATEMENTS --------------
 
--> Beginning of the day represents the resturant in its opening state
pred beginning_of_day {
  always valid_state
  table_init
  server_init
  customer_init
  party_init
}

// run {beginning_of_day} for 5 Int, exactly 7 Person, exactly 5 Customer, exactly 2 Server, exactly 4 Table

--> customers_transition_with_party shows customers transitioning through the CustomerStatus states with their parties - nothing else is monitored here 
pred customers_transition_with_party {
  beginning_of_day
  always {
    some p: Party {
      customerTransistion[p]
    }
  }
}

// run {customers_transition_with_party} for 5 Int, exactly 7 Person, exactly 5 Customer, exactly 2 Server, exactly 4 Table, exactly 2 Party

--> customer_lifcycle takes one party through a resturant lifecycle 
pred customer_lifcycle {
  beginning_of_day
  wellformed
  some p: Party | {always run_states[p]}
}

// run {seat_customers} for 5 Int, exactly 7 Person, exactly 5 Customer, exactly 2 Server, exactly 4 Table, exactly 2 Party

pred seat_first{
  beginning_of_day
  {some p: Party {
    seat[p]
  }} until {all_parties_seated}
}

run {customer_lifcycle} for 5 Int, exactly 7 Person, exactly 5 Customer, exactly 2 Server, exactly 4 Table, exactly 2 Party

