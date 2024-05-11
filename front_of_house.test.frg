#lang forge
//assert and is sat/unsat/ is theorem

open "front_of_house.frg"

pred invalidState { some t: Table | {
    t in Available.tables and t in Full.tables }
}
-------- VALID_STATE TESTS --------
pred wrapperInvalid {not invalidState}
test suite for valid_state {

  assert wrapperInvalid is necessary for valid_state
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

test suite for kitchen_init{ 

}

----------- ORDER_TICKET TESTS -----------

test suite for order_ticket{

}

----------- SERVE_TICKET TESTS -----------

test suite for serve_ticket{
  
}

test suite for beginning_of_day {
  assert valid_state is necessary for beginning_of_day
  assert table_init is necessary for beginning_of_day
  assert server_init is necessary for beginning_of_day
  assert customer_init is necessary for beginning_of_day
  assert party_init is necessary for beginning_of_day
  assert kitchen_init is necessary for beginning_of_day
}
