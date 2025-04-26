Analysis
========
* the dependency graph is generally correct
* the loop yet uses the variable of the init node, 
  * but should use the variable of the component node
  * which is should be inited with the variable of the init node

Solution 1
==========
* init node should be renamed to accumulator node
* component root should not have an associated variable, use the one of the accumulator node instead
* depending on the accumulator is now as depending on the init node variable
* the dependency graph stays feaseable

Solution 2
==========
* depend on component root instead of init node
* display the dependency to an init node as straight (non-dashed) line
* the dependency graph looks suspicious because we will have nodes depending on there predecessors