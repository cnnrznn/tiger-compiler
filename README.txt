Team Members:

Pushyami Kaveti
Connor Zanin

Final Project Integration
-------------------------
This folder contains our compiler written for Tiger. In this project we have implemented the procEntryExit 
functions which wrap the function body to save and restore temps before and after the function body, to pass
proper liveness information for register allocator and add prologue & epilogue to the function.

We have also implemented the following helper functions to make the debugging easier.
1. show() in MakeGraph.sml :          A function which takes output stream and Control Flow Graph and prints out the 
                                      node information for each node.The node information has node name, predeccessors,
                                      successors, use list and def list.

2. show () in Liveness.sml :          A function which takes out stream and an interference graph and prints out the 
                                      adjacent nodes for each node in the graph. This give information about the 
                                      interferendces between nodes. 

3. showWorklists() in Color.sml :     A function which prints out the nodes in the worklists used during register 
                                      coloring.

4. showLiveout() in RegAlloc.sml :    A function takes as input the mapping between control flow graph nodes and live out 
                                      variable at those nodes and print outs this information. the mapping is obtained as 
                                      an output from building an interference graph in Liveness.sml


Some other functions implemented are
1. isDupMove() in RegAlloc.sml :          This function is used to find the redundant moves where the source and 
                                          destination are same registers and delete them from the final assembly code.
2. getAllocatedRegister() in main.sml :   This function is used to get the approriate register allocated for each temp 
                                          present in the assembly instructions. This is used to replace the temps with 
                                          allocated registers in the final assembly code

run instructions:

We included sources.cm, factorial.tig and the corresponding assembly program factorial.tig.s in the .tar file.
We also have a run.sml to compile the .tig files

1. cd tiger-compiler/
2. sml run.sml



