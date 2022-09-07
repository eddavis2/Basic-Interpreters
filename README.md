# Basic-Interpreters
QBASIC-like interpreters, implemented in Basic

bintqb.bas is the QB64 version

bintfb.bas is the FreeBasic version

Both interpret a QBASIC subset.

Note that these are *pure* interpreters - they don't tokenize and/or create any intermediate representation.  They just interpret the source as is.

bintqb running a Tiny Basic interpreter, that is itself written in GW-Basic:

![image](images/bintqbgw.png)

Same, and now loading an running Tiny Star Trek into gw, who is being interpreted by bintqb:

![image](images/bintqbgwstrek.png)
