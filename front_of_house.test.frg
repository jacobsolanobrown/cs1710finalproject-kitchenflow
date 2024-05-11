#lang forge
//assert and is sat/unsat/ is theorem

open "front_of_house.frg"
open "normal_kitchen_queue.frg"

-------- VALID_STATE TESTS --------
pred invalidState0 { some t: Table |  t in Available.tables and t in Full.tables}

pred invalidState1 {some t: Table | t.tableNumber <0 or t.tableNumber > 6}

pred wrapperInvalidTable {not invalidState0 and not invalidState1}

test suite for valid_state {
  assert wrapperInvalidTable is necessary for valid_state
  -------- tests based on predicates properties --------
  -- no table exists that is in both Available and Full
  test expect {
    vs_one : {
        some t: Table | {
            valid_state 
            t in Available.tables
            t in Full.tables 
        }
      } is unsat
    }

    -- no table exists that is not in either available or full 
    test expect {
      vs_two : {
        some t: Table | {
          valid_state 
          t not in Available.tables
          t not in Full.tables 
        }
      } is unsat
    }

    -- table numbers must be unique and valid 
    test expect {
      vs_three : {
        some disj t1, t2: Table | {
          valid_state 
          t1.tableNumber = t2.tableNumber
        }
      } is unsat
    }

    -- table number must be between 1 and 6
    test expect {
      vs_four : {
        some t: Table | {
          valid_state 
          (t.tableNumber < 0)
          (t.tableNumber > 6)
        }
      } is unsat
    } 

    -------- example based tests --------
    -- sat ex: 3 Tables | all with diff nums | all customers waiting 
    test expect {
      vs_five : {
        valid_state
        all t1, t2, t3: Table | {
          t1 in Available 
          t2 in Available 
          t3 in Full 
          t1.tableNumber != t2.tableNumber
          t1.tableNumber != t3.tableNumber
          t2.tableNumber != t3.tableNumber
        }
      } is sat 
    } 

    -- unsat ex: not all tables have a status 
    test expect {
      vs_six: {
        valid_state
        some t1, t2, t3: Table | {
          t1 in Available
          t2 in Available
          TableStatus = Available
        }
      } is unsat 
    } 

     -- unsat ex: customer status is none 
    test expect {
      vs_seven: {
        valid_state
        some c: Customer | {
          c.status = none 
        } 
    } is unsat 
  }
}

---------- SERVER_INIT TESTS ----------

test suite for server_init {
    -------- tests based on predicates properties --------
  -- a table can only 'belong' to one server 
    test expect {
      server_one : {
        server_init
        some disj s1, s2: Server | {
          some t: Table | {
            t in s1.myTables 
            t in s2.myTables
          }  
        }
      } is unsat
    } 

    -- too many servers in resturant 4 the tables! 
    test expect {
      server_two : {
        valid_state
        server_init
        table_init
        all t: Table, s: Server | {
          #{t} < #{s}
        }
      } is unsat
    }

    -- table does not have server
    test expect {
      server_three : {
        valid_state
        server_init
        table_init
        #{Server.myTables} != #{Table}
      } is unsat
    }

    -------- example based tests --------
    test expect {
      server_four : {
        valid_state
        server_init
        table_init
        some s1, s2: Server, t1, t2: Table | {
          s1.myTables = t1
          s2.myTables = t2
        }
      } is sat
    }
}

----------- TABLE_INIT TESTS -----------

test suite for table_init {
  -------- tests based on predicates properties --------
  -- no tables can be in full in init state 
  test expect {
      table_one : {
        table_init 
        valid_state
        some t: Table | {
          t in Full.tables
        }
      } is unsat
  }

  -- no orderes in init state 
  test expect {
    table_two : {
      table_init
      some t: Table | {
        t.orders != none 
      }
    } is unsat
  }

  -- no orders in init state 
  test expect {
    table_three : {
      table_init
      some t: Table | {
        #{t.orders} > 0
      }
    } is unsat
  }

  -- table capacity makes sence 
  test expect {
    table_four : {
      table_init
      some t: Table | {
        t.capacity < 0 
      }
    } is unsat 
  }

  -------- example based tests --------
   test expect {
    table_five : {
      table_init
      some t1, t2: Table | {
        Available.tables = t1 + t2
        t1.capacity = 4
        t2.capacity = 2
      }
    } is sat 
   }

    test expect {
        table_six : {
          table_init
          some t1, t2: Table | {
            Available.tables = t1 + t2
            t1.capacity = -1
          }
        } is unsat 
  }
}

----------- PARTY_INIT TESTS ----------
-------- tests based on predicates properties --------

test suite for party_init {
  -- no party has a size firld that dosen't equal the number of people in the party 
  test expect {
    party_one : {
      party_init
      some p: Party | {
        #{p.people} != {p.size}
      }
    } is unsat
  }  

  -- no customer can be in two parties 
  test expect {
    party_two: {
      party_init
      some c: Customer | {
        one disj p1, p2: Party | {
          c in p1
          c in p2
        }
      }
    } is unsat 
  }

  -------- example based tests --------
  test expect {
    party_three: {
      party_init
      some c1, c2, c3: Customer | {
        some p1: Party | {
          c1 in p1.people
          c2 in p1.people 
          c3 in p1.people
          p1.size = 3 
        }
      }
    } is sat 
  }
}


----------- CUSTOMER_INIT TESTS -----------

test suite for customer_init {
  -------- tests  on predicates properties --------

  -- all must be waiting 
  test expect {
    customer_one: {
      customer_init
      some c: Customer | {
        c.status = Seated or 
        c.status = Ordered or 
        c.status = Ready4Check
      }
    } is unsat 
  }

  -------- example based tests --------

  -- general ex  
  test expect {
    customer_two: {
      customer_init
      some c1, c2: Customer, p1: Party | {
        c1 in p1.people
        c2 in p1.people
        c1.status = Waiting 
        c2.status = Waiting
      }
    } is sat  
  }  
}

----------- KITCHEN_INIT TESTS -----------

test suite for kitchen_init { 
  -- no orders are placed in init state
test expect {
  kitchen_one: {
    kitchen_init
    some k: Kitchen | {
      Kitchen.placedOrder != none 
    }
  } is unsat 
}

test expect {
  wellformedKitchen_init: {
  kitchen_init
} is sat 
}

      -- no orders are placed in init state
test expect {
  kitchen_two: {
    kitchen_init
    some k: Kitchen | {
      Kitchen.placedOrder != none 
    }
  } is unsat 
}
}

pred valid_kitchen_init {
  Kitchen.placedOrder = none
  next = none->none
}

pred not_invalid_kitchen_init {
  not invalid_kitchen_init
}

assert valid_kitchen_init is necessary for kitchen_init
assert not_invalid_kitchen_init is necessary for kitchen_init

----------- ORDER TESTS -----------
test suite for order {
  
  test expect {
    //checking that the party's table stays the same
    validOrder0: {
        one p: Party, t1: Table| {
          p.spot.orders = none 
          p.spot in Full.tables 
          p.spot = t1
          order[p] 
          p.spot = t1
      }
    } is sat

    // the party's table is not supposed to change when an order takes place
    invalidOrder0: {
          one p: Party {
            some disj t1, t2: Table | {
              p.spot.orders = none 
              p.spot in Full.tables 
              p.spot = t1
              order[p] 
              p.spot = t2
            }
        }
    } is unsat

    // checking that a customer's state is updated after they order 
    validOrder1: {
    some p: Party, c: Customer | {
      c in p.people
      c.status = Seated 
      order[p]
      c.status' = Ordered
    } 
    } is sat

    invalidOrder1: {
      some p: Party, c: Customer | {
        c in p.people
        c.status = Seated 
        order[p]
        c.status' = Seated
      } 
    } is unsat

    invalidOrder2: {
      some p: Party, c: Customer | {
        c not in p.people
        c.status = Seated 
        order[p]
        c.status' = Ordered
      } 
    } is unsat
  }
}

----------- ORDER_TICKET TESTS -----------

test suite for order_ticket{
  test expect {
    validTicketOrder0: {
      one p: Party, o: Ticket {
        order_ticket[p] implies {
        kitchen_init
        no p.spot.orders
        all c: Customer | {
          c in p.people implies c.status != Seated
        }
        one k: Kitchen | {
          k.placedOrder = o
        }
        }
      }
    } is sat

    invalidTicketOrder1: {
      some p: Party, o: Ticket, k: Kitchen | {
        order_ticket[p] 
        k.placedOrder = none and k.placedOrder' = none
        p.spot.orders = o.foodOrder
        p.spot.orders' != o.foodOrder
      }
    } is unsat 
  }

}

//TODO
test suite for serve_ticket{}
//TODO
test suite for leave{}

----------- SERVE_TICKET TESTS -----------
//TODO 
test suite for serve_ticket{
  
}

--------------- SEAT TESTS ---------------

test suite for seat {
  -- testing gaurd: party cannot be assigned a table already
  test expect {
    seat_one: {
      some p: Party, t: Table  | {
        p.spot = t
        seat[p]
      }
    } is unsat
  } 
}

--------------- ORDER TESTS --------------

test suite for order {
  -- testing guard: no orders can be @ the table
  test expect {
    order_onw: {
      some p: Party, d: Dish | {
        p.spot.orders = d
        order[p]
      }
    } is unsat
  } 

  --testing guard: table must be full/assigned 
  test expect {
    order_two: {
      some p: Party, d: Dish | {
        beginning_of_day
        p.spot != none
        order[p]
      }
    } is unsat
  } 
}

--------------- EATING TESTS --------------

test suite for eating {
  -- testing guard: making sure that kitchen has an order
  test expect {
    eating_one: {
      some t: Ticket, p: Party | {
        eating[p]
        Kitchen.placedOrder = none
      }
    } is unsat
  } 

   test expect {
    //states need to update correctly
    validEating0: {
      some p: Party | {
        all c: Customer | {
          c in p.people
          c.status != Ready4Check
          eating[p]
          c in p.people implies c.status = Ready4Check
        }

      }
    } is sat

    //states need to updated correctly, cannot have someone ready4check before having food and eating
    invalidEating0: {
      some p: Party | {
        some c: Customer | {
          c in p.people 
          c.status = Ready4Check 
          eating[p]
          c.status = Waiting
        }
      }
    } is unsat

    invalidEating1: {
      some p: Party | {
        eating[p] and not serve_ticket[p]
      }
    } is unsat

    validTable: {
      some p: Party, t: Table| {
        p.spot = t
        eating[p]
        p.spot' = t
      }
    } is sat
  }
}

--------------- LEAVE TESTS --------------

test suite for leave {
  

}

---------- BEGINNING OF DAY TESTS ---------

test suite for beginning_of_day {
  assert valid_state is necessary for beginning_of_day
  assert table_init is necessary for beginning_of_day
  assert server_init is necessary for beginning_of_day
  assert customer_init is necessary for beginning_of_day
  assert party_init is necessary for beginning_of_day
  assert kitchen_init is necessary for beginning_of_day
}
