# Logic 4 Systems Final Project by @lmckeown, @mmack1 & @gsolano
<ln/>
# Resturant Flow

TODO: write short summary for a few stakeholders in ReadMe!  
TODO: demo day --> Create a visual via slides to aid in the presentation | Make it fun 

What we are modeling: 

The team - Lauren, Liliana, and Jacob - all worked at restaurants during the COVID-19 pandemic. Now for our final project, we will be modeling a restaurant to learn more about the complexities of the restaurant kitchen flow! Given a normal sit-down-and-order restaurant that has different table sizes, a limited kitchen staff, and a menu of appetizers and main course meals, we want to model that using Forge. In modeling the kitchen flow, we want to see how appetizers and main meals come out for small vs. big groups. In our model, we will explore how different customer service strategies change the success of the restaurant. 

COMPONENTS: 

PERSON (abstract sig)
- Customer (extends person)
- Chef (extends person)
- Waiter (extends person)

TABLES (sig)
- Availability
- Orders (sig)
- Server 
- Customers
- Dish Type (enum) (each item)

KITCHEN (sig)
- Queue
- Chef
- Orders
- Tables

We will engage with Computer Science Models in our Kitchen Queue 
- the first iteration of the kitchen queue will be a first in first out that takes in orders
- the second iteration of the kitchen queue will be a priority-based queue that takes in tables with different orders 
  
Questions from Tim: 

1. What tradeoffs did you make in choosing your representation? What else did you try that didn’t work as well?

2. What assumptions did you make about scope? What are the limits of your model?

3. Did your goals change at all from your proposal? Did you realize anything you planned was unrealistic, or that anything you thought was unrealistic was doable?

4. How should we understand an instance of your model and what your visualization shows (whether custom or default)?

