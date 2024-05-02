#lang forge
option problem_type temporal 

abstract sig Person {}

sig Customer extends Person {
  // can either be empty or contain exactly one
  myTableNumber: lone Table 
}

abstract sig CustomerStatus {
   customersInStatus: set Customer
}
one sig Waiting, Seated, Ordered, Ready4Check extends CustomerStatus {}

sig Server extends Person {
  // tables: set Table
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
one sig Available, Full extends TableStatus {}

/*
Initializes tables at the beginning of the day --> they are all available with no one at them!  
*/
pred valid_state {
  -- Tables are either full or occupied, cannot be both
  Table = Available.tables + Full.tables
  no t : Table | t in Available.tables and t in Full.tables

  -- Customers are either waiting for a table, seated, ordered or ready for the check, TODO: cant be both
  Customer = Waiting.customersInStatus + Seated.customersInStatus + Ordered.customersInStatus + Ready4Check.customersInStatus

 -- tables numbers cannot be negative / need to be in a specific range (1-5)


}

pred table_init {
  // table init specs: 
  // - each table has a unique table number [1-X]
  // - each table is avaibale 
  // - no customers are at any table

  // each table is avaibale
  Table = Available.tables + Full.tables
  Table = Available.tables

  // no customers at any table & no customers have an assigned table number
  all c: Customer | no c.tn
  #{c: Customer | c in Table.customers} = 0

  //each table has a unique table #
  all disj t1, t2: Table | {
    //assign unique table number 
    //TODO: limit table number scope?
    t1.tableNumber > 0 implies {
    t1.tableNumber != t2.tableNumber
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

pred table_setup {
  valid_table_init
}

run {table_setup} for 5 Int, exactly 4 Table
