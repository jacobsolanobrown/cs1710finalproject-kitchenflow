#lang forge
//assert and is sat/unsat/ is theorem

open "front_of_house.frg"

test suite for valid_state {
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
}

test suite for server_init {
  -- a table can only 'belong' to one server 
    test expect {
      server_two : {
        server_init
        some disj s1, s2: Server | {
          some t: Table | {
            t in s1.myTables 
            t in s2.myTables
          }  
        }
      } is unsat
    } 
}

test suite for table_init {
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
}

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
}

test suite for customer_init {
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
}


test suite for kitchen_init{ 

}

test suite for order_ticket{

}

test suite for serve_ticket{
  
}
