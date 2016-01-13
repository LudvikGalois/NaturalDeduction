# NaturalDeduction
A Natural Deduction Proof assistant for emacs

Probably has lots of bugs, but none of them should let you do anything dodgy;
you might just crash it. (It's also possible there are some proofs you can't
write with it, since I didn't look too closely at the notation being used,
and mostly just guessed what it should mean, then read some example proofs,
and made sure they could be entered

To use, just load it into emacs (i.e M-x load-file <ret> path-to-this-file <ret>)
and then run M-x natural-deduction-proof. It should be pretty self explantory from
there. Although the first thing you might notice is that you enter formulae connective
first, and everything is right associative. i.e to enter something like (p∨¬q)∧r
you'd type the key sequence A-O-V-P-RET-N-V-Q-RET-V-R-RET
