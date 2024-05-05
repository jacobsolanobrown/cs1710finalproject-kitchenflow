#lang forge
option problem_type temporal 

//default trace length is 5 -- could enforce a new max thats a bigger number 

abstract sig Person {}

sig Customer extends Person {
  // can either be empty or contain exactly one
  myTableNumber: lone Table, 
  var status: one CustomerStatus
  //should each customer have an order?? instead of having orders in the Table sig
}


sig Party {
  people: set Customer,
  size: one Int, 
  spot: one Table
}

abstract sig CustomerStatus {}
one sig Waiting, Seated, Ordered, Ready4Check extends CustomerStatus {} //state changes

sig Server extends Person {
  myTables: set Table
  //not sure if we need this
  // activeOrders: set Dish
}

sig Table {
  tableNumber: one Int,
  customersAtTable: set Customer, 
  capacity: one Int
  // server: one Server,
  // orders: set Dish,
  // price: lone Int
}

abstract sig TableStatus {
   tables: set Table
}
one sig Available, Full extends TableStatus {} // state changes 

/*
Ensures that each state is valid - no crazy instances
*/

--> Tables are either Available OR Full | can't be both
--> Customers are either Waiting or Seated or Ordered or Ready4Check | can't be in more than one 
--> Table numbers must be positive/in a specific range [1-5]
--> Each Table should have a unique table number
--> ?? need to state how many people are in the resturant 

pred valid_state {
  --> Tables are either full or occupied, cannot be both
  Table = Available.tables + Full.tables
  no t : Table | t in Available.tables and t in Full.tables

 --> Tables numbers cannot be negative / need to be in a specific range (1-5)
 all t: Table | t.tableNumber > 0 and t.tableNumber < 6

 --> Each table has a unique table #
  all disj t1, t2: Table | {
    //assign unique table number 
    //TODO: limit table number scope?
    // previously, t1.tableNumber > 0 and t1.tableNumber < 6 implies 
    t1.tableNumber != t2.tableNumber // I think this is better 
  }
}

/*
The following preds work together to Initialize Resturant at the beginning of the day | Opening State 
-- TABLE INIT
-- CUSTOMER INIT 
-- PARTY INIT 
-- SERVER INIT
-- TODO: KITCHEN INIT
*/

pred table_init {
  --> All Tables are available
  Table = Available.tables

  --> No customers at any table
  all t: Table | {
    no c : Customer | c in t.customersAtTable
  }

  --> Setting capacity to specified range {2, 4}
  all t: Table | {
    t.capacity = 2 or t.capacity = 4
    // when the place opens, no one is at the table yet, they are all waiting
    #{c: Customer | c in t.customersAtTable} = 0
  }
}

pred customer_init {
    --> All Customers are Waiting (none are in the resturant yet)
    all c: Customer | c.status = Waiting

    --> each customer is part of ONE party 
    // [unsat] all c: Customer | one p: Party | {c in p.people}
}

pred party_init {
  --> each customer is apart of one party

  --> party is not at a table yet - denoted by -1
  --> party size is greater than 0 
  --> customer set is equal to party size
  all p: Party | {
    #{p.size} > 0
    #{p.people} = #{p.size}
    p.spot = -1
  }
}

pred server_init {
  --> Not more servers than tables
  valid_state implies {
    all s: Server, t: Table | {
      #{s} <= #{t}
    }
  }
  --> each table only has one server
  all disj s1, s2: Server | {
    s1.myTables != s2.myTables
    no t: Table | t in s1.myTables and t in s2.myTables // this might be better 
  }
}

// matches table to group size
pred find_table[p: Party, openTables: set Table] { 
  all t: openTables{
    {p.size <= t.capacity} 
  }
  all c: p.people {
    c.myTableNumber = p.people
  }
}

// seats customers at table
pred occupy_table[p: Party] {
  find_table[p, Available.tables]
  all t: Table, p: Party | { 
      #{c: Customer | c in p.people} <= t.capacity
    }

}
// seats customers at table
// pred occupy_table[p: Party] {
//   find_table[p, Available.tables]
//   all t: Table, p: Party | { 
//       #{c: Customer | c in p.people} <= t.capacity
//     }
// }

// pred occupy_table[t: Table] {
//   --> occupy with two customer 
//   {t in Available.tables => {
//     --> customer has to go from waiting to seated 
//     --> table has to go form available to taken 
//     some a: Customer | {
//       a.status = Waiting
  
//       t.customersAtTable' = t.customersAtTable + (a)
//       a.status' = Seated
  
//       Available.tables' = Available.tables - t
//       Full.tables' = Full.tables + t
//     }}}  
// }

//unseats customers at table 
pred vacate_table {

}

//TODO: how to transition between states in a manner where Waiting -> Seated -> Ordered -> Ready4Check

pred customerTransistion {
  some c: Customer | {
    // some changed: CustomerStatus | {
      c.status = Waiting => c.status' = Seated
      c.status = Seated => c.status' = Ordered
      c.status = Ordered => c.status' = Ready4Check
      c.status = Ready4Check => c.status' = Waiting
      all other: Customer-c | other.status = other.status' }
}


// minimum that each table orders just one order of either a burger, salas, or chicktenders
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

// pred table_setup {
//   valid_state
//   table_init
//   server_init
//   customer_init
//   one p: Party, t: Available | {
    
//     // #{p.people} > 0 //people in party greater than one
//     // #{p.people} = p.size //party size equal to people 
//     find_table[p, Available.tables]
//   }
//   always customerTransistion
// }

// run {table_setup} for 5 Int, exactly 2 Customer, exactly 4 Table

pred beginning_of_day {
  always valid_state
  table_init
  server_init
  customer_init
  always customerTransistion
}

// run {table_setup} for 5 Int, exactly 4 Table
//   party_init
//   customer_init
//   customerTransistion
//   // one t: Available.tables | {
//   //   occupy_table[t]
//   // }
//   // always customerTransistion
// }
run {beginning_of_day} for 5 Int, exactly 7 Person, exactly 5 Customer, exactly 2 Server, exactly 4 Table

