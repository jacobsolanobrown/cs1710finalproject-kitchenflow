#lang forge
option problem_type temporal 

abstract sig Person {}

sig Customer extends Person {
  // can either be empty or contain exactly one
  myTableNumber: lone Table 
  //should each customer have an order?? instead of having orders in the Table sig
}

abstract sig CustomerStatus {
   customersInStatus: set Customer
}

one sig Waiting, Seated, Ordered, Ready4Check extends CustomerStatus {} //state changes

sig Server extends Person {
  myTables: set Table
  //not sure if we need this
  // activeOrders: set Dish
}

sig Table {
  tableNumber: one Int,
  customersAtTable: set Customer
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

  --> Customers are either waiting for a table, seated, ordered or ready for the check
  Customer = Waiting.customersInStatus + Seated.customersInStatus + Ordered.customersInStatus + Ready4Check.customersInStatus
  // TODO: cant be both - ugh this is gonna be like 7 lines of math :/

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

// not more servers than tables
// not more than one to a table
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
/*
Initializes Resturant at the beginning of the day | Opening State 
--> All Tables are available
--> All Customers are Waiting (none are in the resturant yet)
--> The kitchen queues should be empty 
*/
pred table_init {
  --> Each table is avaibale
  Table = Available.tables

  --> No customers at any table & no customers have an assigned table number: MIGHT NEED TO FIX 
  all c: Customer | {
    c in Available.tables
  }
  
  // not sure if i need this?
  #{c: Customer | c in Table.customersAtTable} = 0


  --> TODO: Kitchen queue should be empty
}

//TODO: how to transition between states in a manner where Waiting -> Seated -> Ordered -> Ready4Check
// use the next state ' notation but that can we do with that 

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

pred table_setup {
  valid_state
  table_init
  server_init

}

run {table_setup} for 5 Int, exactly 4 Table
