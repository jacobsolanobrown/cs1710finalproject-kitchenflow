#lang forge
//assert and is sat/unsat/ is theorem

open "front_of_house.frg"

test suite for valid_state {
  // test expect { possibleToMove: {
  //   valid_state
  //   #{Table} = add(#{vailable.tables}, #{Full.tables}) 
  // } is theorem }  
}

test suite for server_init {
    test expect { possibleToMove: {
    valid_state
    #{Table} = add(#{vailable.tables}, #{Full.tables}) 
  } is theorem } 
}

test suite for table_init {
  test_expect {
    
  }
}

// test suite for  

test suite for kitchen_init{ 

}

test suite for order_ticket{

}

test suite for serve_ticket{
  
}
