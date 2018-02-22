Members:

  Pushyami Kaveti
  Connor Zanin

Handling break:

when break statement is encountered, the immediate enclosing loop (while or For) is terminated and the program resumes at the next statement following the loop.If there is no enclosing loop it is illegal to have the break statement. 
To handle this we keep a variable called 'loopLevel' which is incremented when we enter a loop and decremented when we exit the loop.The loopLevel os initialilzed to 0 at the beginning type checking. If we encounter a break statement when loopLevel is 0, it means that there is no enclosing loop. Hence, we throw an error. Otherwise, we proceed with the typecheck.


