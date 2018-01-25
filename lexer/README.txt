Members:
  Pushyami Kaveti
  Connor Zanin

Comments:
  The lexer begins in the 'INITIAL' state.
  If the pattern "/*" is matched, we transition to  the 'COMMENT' state.
  In the COMMENT state, we keep track of the nest level of the comment with the 'comlevel' variable.
  Open comment sequences increment this value; likewise, close comment sequences decrement the value.
  When entering the top-level comment, comlevel is set to 1.
  If we decrement the comlevel to 0, the lexer returns to the 'INITIAL' state.
  Otherwise, we have an open-ended comment.
  We discuss how this is handled in the 'EOF' section.

Errors:
  Our lexer has four start states: INITIAL, COMMENT, STRING, ESC.
  Handling errors is discussed separately for each start state.

  INITIAL:
    In the initial (i.e. "code"), state, we match identifiers, white-space, newlines, and integer literals.
    As well, we recognize open comment or open string to transition start states.
    If none of the above is recognized, the location of the offending character (that matches the regex 'dot') is reported, and we continue.

  COMMENT:
    The only way to have an error inside a comment is to reach EOF before closing the comment.

  STRING:
    Within the STRING start state (not within the string itself, errors can occure within escape sequences), the only error is an un-escaped newline.

  ESC:
    - invalid ascii codes (i.e. >127) generate an error
    - formatting sequences that are not "closed", i.e."(non-formatting characters)\fff(formatting characters)fff...(non-formating characters)"
    - any character that is not a valid escape character, e.g. "\y" is not legal

EOF: 
  End of File is detected by matching the last new line character "\n"  in the file and can occur in one of the following states
  - INITIAL : If EOF appears in this state it is considered legal and we return the line number and the total number of chracaters in the file.
  - STRING : If EOF appears while the lexer is in STRING state, it is marked not-legal and reported as an error ("open string/comment").
  - COMMENT : If EOF appears in this state, it is marked not-legal and reported as an error ("open string/ comment"). 

ADDITIONAL:
  We added two additional tokens to accomodate the tiger built-in types 'int' and string'.

  The legal escape characters in our implementation are '\n', '\t', '\"', '\\', '\^C', and '\^Z'.
  The Tiger specification is not clear about what escape characters are legal and what are not.
  For example, we omit '\a' as a legal escape sequence as a design choice.
