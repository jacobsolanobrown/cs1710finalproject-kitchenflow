#lang forge
option problem_type temporal 

//default trace length is 5 -- could enforce a new max thats a bigger number 
//use var to make state variable

------------- DEFINITIONS -------------
-------- Employees & Customers --------

abstract sig Person {}

sig Customer extends Person {
  myTableNumber: lone Table, 
  var status: one CustomerStatus 
}

abstract sig CustomerStatus {}
one sig Waiting, Seated, Ordered, Ready4Check extends CustomerStatus {} //state changes

sig Party {
  people: set Customer,
  size: one Int, 
  spot: one Table
}

sig Server extends Person {
  myTables: set Table
}

---------------- Table ----------------

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
one sig Available, Full extends TableStatus {} 

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
--> Setting capacity to specified range {2, 4}

pred table_init {
  Table = Available.tables

  all t: Table | {
    no c : Customer | c in t.customersAtTable
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

--------------- RESTURANT MANAGEMENT --------------

// matches table to group size -- TODO
pred find_table[p: Party] { 
  --> find a table in available tables that has capacity > party size
  // all t: openTables{
  //   {p.size <= t.capacity} 
  // }
  // all c: p.people {
  //   c.myTableNumber = p.people
  // }
}

// seats customers at table -- TODO: 
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

// every customer transitions 
// pred customerTransistion { //WORK ONLY W/SEATED/ORDERED 
//   //?? change to all customer in the party transition 
//   all c: Customer | {
//       c.status = Waiting => c.status' = Seated
//       c.status = Seated => c.status' = Ordered
//       c.status = Ordered => c.status' = Ready4Check
//       c.status = Ready4Check => c.status' = Waiting
//     }
// }

//customers transition just with their party 
pred customerTransistion[p: Party] { //WORK ONLY W/SEATED/ORDERED 
  //?? change to all customer in the party transition 
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

pred ordering {
  //TODO: JACOB
}

--------------- RUN STATEMENTS --------------

pred beginning_of_day {
  always valid_state
  table_init
  server_init
  customer_init
  party_init
}

// run {beginning_of_day} for 5 Int, exactly 7 Person, exactly 5 Customer, exactly 2 Server, exactly 4 Table

pred customers_transition_noParty {
  always valid_state
  table_init
  server_init
  customer_init
  party_init
  some p: Party {
    always customerTransistion[p]
  }
}

run {customers_transition_noParty} for 5 Int, exactly 7 Person, exactly 5 Customer, exactly 2 Server, exactly 4 Table, exactly 2 Party


