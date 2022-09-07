option explicit

'30 Jul 2022 12:39 pm: Bug! label: load: gets run as load command!!!
'need to distinguish the difference
'------------------------------------------------------------------------
'  03 Jul 2021 todo
'  [x] store/retrieve variables like eval-ed4
'  [x] const id[$] = number|string {, const id[$] = number|string}
'  [ ] consolidate loop handling data structures
'  [x] arrays
'      [x]  parse
'      [x]  allocate 1 dimensional
'      [x]  allocate 2 dimensional
'      [x]  assign (idstmt, stridstmt)
'      [x]  reference (strfactor, primary)
'  [ ] Subs
'  [ ] Functions
'  [ ] Shared variables
'  getvarindex& (getstrindex$), used in:
'  forstmt:    to reference the "i" variable
'  inputstmt:  to reference the "input" variable: input "", numeric_store(i)
'  swapstmt:   reference: swap(numeric_store(i1), numeric_store(i2))
'  assignment: numeric_store(i) = value
'  primary:    primary# = numeric_store(i)
'idstmt (stridstmt) - only called by assignment
'@review:  i = find_vname&(ident) -- lots of common code, can be combined
'------------------------------------------------------------------------
' QBASIC subset interpreter by Ed Davis.
' This is the FreeBasic version of a Simple QBASIC interpreter.
' Almost identical to the QB64 version, except for QB64 extensions.
' Compile with fb -gen gcc -O 3 -lang qb bintfb.bas
'------------------------------------------------------------------------------------------
' Currently supports:
'
' Double and string variables only. No dim for these.
' One or two dimensional arrays.
' All standard operators, with hopefully the correct precedence.
'
' String operators:
' +
' =, <>, <, >, <=, >=
'
'
' Numeric binary operators
' ^,
' *, /
' \
' mod,
' +, -,
' shl,<<, shr,>>
' =, <>, <, >, <=, >=,
' and,
' or,
' xor,
' eqv,
' imp,
'
' Numeric unary operators
' not, -, +
'
' QBASIC stmts:
' ?,
' chdir,
' circle,
' cls,
' color,
' do [until][while] .. loop [until][while]
' draw,
' environ,
' exit,
' files,
' for .. next
' gosub .. return
' goto,
' if - single and multi-line: if elseif else end if or endif
' input,
' line,
' locate,
' mid$,
' paint,
' palette,
' play,
' preset,
' print,
' pset,
' randomize,
' rem,
' screen,
' shell,
' sleep,
' sound,
' swap,
' view,
' while .. wend
' width,
' window,
'
' QBASIC string functions:
'
' chr$,
' command$,
' date$,
' environ$,
' hex$,
' inkey$,
' lcase$,
' left$
' lpad$,
' ltrim$,
' mid$,
' mki$,
' oct$,
' replace$,
' right$
' rpad$,
' rtrim$,
' space$
' str$,
' string$
' time$,
' trim$,
' ucase$,
'
' QBASIC numeric functions
' abs,
' acos,
' acosh,
' acot,
' acoth,
' acsc,
' acsch,
' asc,
' asec,
' asech,
' asin,
' asinh,
' atanh,
' atn, atan,
' cdbl,
' cint,
' clng,
' cos,
' cosh,
' cot,
' coth,
' csc,
' csch,
' csng,
' csrlin,
' cvd,
' cvi,
' exp,
' false,
' frac,
' fix,
' instr,
' int,
' len,
' ln,
' log
' log10,
' point,
' pos,
' rnd
' screen
' sec,
' sech,
' sgn,
' sin,
' sinh,
' sqr, sqrt,
' tan,
' tanh,
' timer,
' true,
' val,
'
' No other numeric data types besides double. Only suffix accepted is $ for strings.
' Only up to two dimensional arrays
' No subs or functions.
' No dim.
' Lots of other stuff missing.
'------------------------------------------------------------------------------------------

declare function accept&(s as string)
declare function any_expr&(p as integer)
declare function bool_expr&
declare function fileexists%(filename as string)
declare function numeric_expr#
declare function numeric_expr2#(p as integer)
declare function find_matching_else$
declare function gettoeol$
declare function instrfun&
declare function is_multi_line_if&
declare function is_stmt_end&
declare function peek_ch$
declare function pop_num#
declare function pop_str$
declare function primary#
declare function storeline&
declare function strexpression$
declare function strfactor$

declare sub clearprog
declare sub clearvars
declare sub colorstmt
declare sub docmd(interactive as integer)
declare sub elsestmt
declare sub endifstmt
declare sub exitstmt
declare sub expect(s as string)
declare sub filesstmt
declare sub find_matching_sline_if
declare sub find_matching_pair(s1 as string, s2 as string)
declare sub forstmt
declare sub getsym
declare sub gosubline(target as integer)
declare sub gosubstmt
declare sub gotoline(target as integer)
declare sub gotostmt
declare sub idstmt
declare sub ifstmt
declare sub initvars
declare sub inputstmt
declare sub lineinputstmt
declare sub linestmt
declare sub liststmt
declare sub loadprog(fn as string)
declare sub locatestmt
declare sub midstmt
declare sub multi_ifstmt(cond as integer)
declare sub nextstmt
declare sub printstmt
declare sub randomizer
declare sub returnstmt
declare sub saveprog
declare sub showhelp
declare sub skiptoeol
declare sub stridstmt
declare sub validlinenum(n as integer)
declare sub wendstmt
declare sub whilestmt(first as integer)

const true = -1, false = 0
const e         = 2.71828182845905
const halfpi    = 1.5707963267949
const pi        = 3.14159265358979
const max_store = 512
const varssize  = 64
const stacksize = 512
const pgmsize   = 6000
const tyunknown=0, tyident=1, tystrident=2, tynum=3, tystring=4
const left_side = 0, right_side = 1

dim shared the_ch as string    ' last char read from input
dim shared sym as string       ' last symbol read
dim shared symtype as integer  ' type of last symbol read
dim shared the_num as double   ' last number read
dim shared pgm(pgmsize) as string ' lines of text stored here
dim shared curline as integer  ' number of current line in pgm
dim shared thelin as string    ' text of current line
dim shared textp as integer    ' positionn in thelin
dim shared errors as integer
dim shared curr_filename as string

type do_loop_t
  lline as integer
  loff  as integer
end type

' do/while/for/if tracking
dim shared loopvars(varssize) as integer, looplines(varssize) as integer
dim shared loopmax(varssize) as double, loopstep(varssize) as double
dim shared loopoff(varssize) as integer
dim shared stackp as integer, loopp as integer
dim shared gosubstack(stacksize) as integer, gosuboffstack(stacksize) as integer
dim shared while_sp as integer, while_line(varssize) as integer, while_off(varssize) as integer
dim shared do_sp as integer, do_loop(stacksize) as do_loop_t
dim shared if_sp as integer, if_stack(stacksize) as integer

' for arrays:  make sure the user specified index is between lo_bnd..hi_bnd inclusive
' then, computed index = v.index + user_index - v.lo_bnd
type names_t
    vname    as string
    symtype  as integer ' variable name
    index    as long    ' index into string table; numeric table; or string/numeric array table
    is_const as integer
    lo_bnd   as long
    hi_bnd   as long
    lo_bnd2  as long    ' only if 2 dimensional
    hi_bnd2  as long    ' only if 2 dimensional
    multi    as integer ' true if 2 dimensional
    a_len    as long    ' non-zero if array
    a_width  as long    ' used in computing index when 2 dimensional
end type

' variable names
dim shared var_names(1 to max_store) as names_t, var_names_max as integer

' string and numeric values
dim shared string_store(1 to max_store) as string, str_store_max as integer
dim shared numeric_store(1 to max_store) as double, num_store_max as integer

' string and numeric arrays
redim shared string_arr_store(0) as string: dim shared str_arr_stor_max as long
redim shared numeric_arr_store(0) as double: dim shared num_arr_stor_max as long

' used by expression parser
dim shared str_stack(varssize) as string
dim shared num_stack(varssize) as double
dim shared str_st_ndx as integer, num_st_ndx as integer

dim shared endif_count as integer
dim shared wend_count  as integer
dim shared next_count  as integer
dim shared loop_count  as integer

dim shared tracing as integer
dim shared stepping as integer
dim shared filenum as long
const right_assoc = 0, left_assoc = 1, unaryminus_prec = 13, unaryplus_prec = 13, unarynot_prec = 6

'for performance timing
'dim shared scantime as double
'dim shared starttime as double
'dim shared nsyms as long

dim shared ctype_arr(255) as integer
const ct_unknown=0, ct_alpha=1, ct_digit=2, ct_period=3, ct_punc1=4
const ct_dquote=5, ct_squote=6, ct_amp=7, ct_lt=8, ct_gt=9, ct_dollar=10

dim shared atarray(1000) as long

'---------------------------------------------------------------------------------------------------
' Listed here since I can not remember them:
' % = integer (16 bit)
' & = long    (32 bit)
' ! = single  (default)
' # = double
' $ = string
'---------------------------------------------------------------------------------------------------
' Maybe add:
' min(x, x1, x2...), max(...), ave(...), sum(...)
'#define floor(x) ((x*2.0-0.5)shr 1)
'#define ceil(x) (-((-x*2.0-0.5)shr 1))
'---------------------------------------------------------------------------------------------------

call init_scanner
tracing = false
stepping = false

str_st_ndx = 0
num_st_ndx = 0

'------------------------------------------------------------------------
' main loop
'------------------------------------------------------------------------
dim cmd$
dim quit as integer
quit = false

'starttime = timer
cmd$ = command$
if command$(1) = "-t" then
    cmd$ = ltrim$(rtrim$(mid$(command$, 4)))
    if cmd$ <> "" then quit = true
end if

if cmd$ = "" then
  call showhelp
else
  if fileexists%(cmd$) then
    pgm(0) = "run " + chr$(34) + cmd$ + chr$(34)
    call initgetsym(0, 1)
    call docmd(false)
  else
    pgm(0) = cmd$
    call initgetsym(0, 1)
    call docmd(true)
  end if
end if

if quit then call showtime: if errors then system 1 else system

do
  line input "> ", pgm(0)
  if pgm(0) <> "" then
    call initgetsym(0, 1)
    call docmd(true)
  end if
loop

' show timings
sub showtime
  'dim total_time as double
  'total_time = timer - starttime

  'print "Total time: "; total_time; " Scan time: "; scantime; " Parse time: "; total_time - scantime; " Symbols: "; nsyms
  'sleep
end sub

function at_line$
  at_line$ = "": if curline > 0 then at_line$ = "(" + str$(curline) + ")"
end function

function rest_of_line$
  rest_of_line$ = sym + " " + the_ch + " " + mid$(thelin, textp)
end function

sub dump_tables
  dim i as integer

  print "name", "index", "lo", "hi", "len"
  for i = 1 to var_names_max
    print var_names(i).vname, var_names(i).index, var_names(i).lo_bnd, var_names(i).hi_bnd, var_names(i).a_len
  next
end sub

'------------------------------------------------------------------------
' command processor
'------------------------------------------------------------------------
sub docmd(interactive as integer)
'print "docmd"
  errors = false

  restart_loop:
  stackp = 0    ' these were -1 ??? @review
  loopp   = 0   ' these were -1 ??? @review
  while_sp = 0
  do_sp = 0
  if_sp = 0

  do
    loop_top:
    if errors then exit sub
    while sym = "" and curline > 0 and curline < pgmsize
      call initgetsym(curline + 1, 1)
    wend
    if tracing then print "["; curline; "] "; sym; " "; the_ch; " "; ltrim$(mid$(thelin, textp))
    if stepping then sleep
    select case sym
      case "":            exit sub
      case "bye", "quit": call getsym: call showtime:  if errors then system 1 else system
      case "clear":       call getsym: call clearvars: exit sub
      case "edit":        call getsym: call editstmt:  exit sub
      case "help":        call getsym: call showhelp:  exit sub
      case "list":        call getsym: call liststmt:  exit sub
      case "load", "old": call getsym: call loadprog(""):  exit sub
      case "new":         call getsym: call initvars: call clearprog: tracing = false: exit sub
      case "reload":      call getsym: call loadprog(curr_filename): exit sub
      case "run":         call getsym: call runprog: interactive = false: goto restart_loop
      case "save":        call getsym: call saveprog:  exit sub
      case "stop", "end", "system": call getsym:       exit sub
      case "dump":        call getsym: call dump_tables

      case "chdir":       call getsym: call chdircmd
      case "circle":      call getsym: call circlestmt
      case "close":       call getsym: call closestmt
      case "cls":         call getsym: cls
      case "color":       call getsym: call colorstmt
      case "const":       call getsym: call conststmt
      case "dim":         call getsym: call dimstmt
      case "do":          call getsym: call dostmt(true)
      case "draw":        call getsym: call drawstmt
      case "else":        call getsym: call elsestmt
      case "elseif":      call getsym: call elseifstmt
      case "endif":       call getsym: call endifstmt
      case "environ":     call getsym: call environstmt
      case "exit":        call getsym: call exitstmt
      case "for":         call getsym: call forstmt
      case "gosub":       call getsym: call gosubstmt: goto loop_top
      case "goto":        call getsym: call gotostmt:  goto loop_top
      case "if":          call getsym: call ifstmt:    goto loop_top
      case "input":       call getsym: call inputstmt
      case "line":        call getsym: call lineinputstmt
      case "loop":        call getsym: call loopstmt
      case "locate":      call getsym: call locatestmt
      case "mid$":        call getsym: call midstmt
      case "next":        call getsym: call nextstmt
      case "open":        call getsym: call openstmt
      case "paint":       call getsym: call paintstmt
      case "palette":     call getsym: call palettestmt
      case "preset":      call getsym: call presetstmt
      case "print", "?":  call getsym: call printstmt
      case "pset":        call getsym: call psetstmt
      case "randomize":   call getsym: call randomizer
      case "rem", "'":    call getsym: call skiptoeol
      case "return":      call getsym: call returnstmt: goto loop_top
      case "screen":      call getsym: call screenstmt
      case "shell":                    call shellstmt
      case "sleep":       call getsym: call sleepstmt
      case "swap":        call getsym: call swapstmt
      case "view":        call getsym: call viewstmt
      case "wend":        call getsym: call wendstmt
      case "while":       call getsym: call whilestmt(true)
      case "width":       call getsym: call widthstmt
      case "window":      call getsym: call windowstmt

      'case "screenres":   call getsym: call screenresstmt

      case "@":           call getsym: call atassn

      case "troff": call getsym: tracing  = false
      case "tron":  call getsym: tracing  = true
      case "stoff": call getsym: stepping = false
      case "ston":  call getsym: stepping = true

      ' need to account for:
      '  - assignment
      '    let ...
      '    [str]ident = expression
      '    [str]ident(expression [, expression]) = expression
      '  - labels
      '    ident:
      '  - non-assignment, including labels
      '
      case else
        if left$(sym, 1) = "_" then
          print "Unknown command: "; sym: errors = true
        elseif accept&("let") then
          call assignment
        elseif symtype = tyident or symtype = tystrident then
          if peek_ch$ = "=" then
            call assignment
          elseif peek_ch$ = "(" and instr(mid$(pgm(curline), textp), "=") > 0 then
            call array_assignment
          elseif symtype = tyident and the_ch = ":" then
            call getsym
          elseif interactive then
            call printstmt
          elseif sym <> ":" and sym <> "" then
            print at_line$; "Stmt expected, found:"; rest_of_line$: errors = true
          end if
        elseif interactive then
          call printstmt
        elseif sym <> ":" and sym <> "" then
          print at_line$; "Stmt expected, found:"; rest_of_line$: errors = true
        end if
    end select

    if errors then
      exit sub
    elseif sym = ":" then
      call getsym
    elseif sym <> "else" and sym <> "" then
      print at_line$; "Extra stmts:"; rest_of_line$: errors = true
      print "symtype:"; symtype; " sym:"; sym; " ch:"; the_ch
    end if
  loop
end sub

'------------------------------------------------------------------------
' variable storage/retrieval
'------------------------------------------------------------------------

' find position of vname in var_names
function find_vname&(vname as string)
  dim i as integer

  for i = 1 to var_names_max
    if var_names(i).vname = vname then
      find_vname& = i
      exit function
    end if
  next

  find_vname& = 0
end function

' helper function for 2d arrays
function ar_scale(i as long, lo as long)
  ar_scale = i - (lo - 1)
end function

' get the index of "a" in either string_arr_store or numeric_arr_store
' pointing to: a(expr [, expr])
function get_array_index&(ident as string)
  dim i as integer, index as long, index2 as long, lo as long, lo2 as long
  dim x as long

  call getsym
  i = find_vname&(ident)
  if i = 0 then print at_line$; "Array has not been declared: "; ident: errors = true: exit function
  expect("(")
  index = numeric_expr#

  if var_names(i).multi then
    expect(",")
    index2 = numeric_expr#
  end if

  expect(")")
  if var_names(i).a_len = 0 then
    print at_line$; "'"; ident; "' is not declared as an array": errors = true: exit function
  end if

  ' verfiy that the index is within range
  if index < var_names(i).lo_bnd or index > var_names(i).hi_bnd then
    print at_line$; "Index is out of range:"; index; "("; var_names(i).lo_bnd; ","; var_names(i).hi_bnd; ")": errors = true: exit function
  end if
  if var_names(i).multi then
    if index2 < var_names(i).lo_bnd2 or index2 > var_names(i).hi_bnd2 then
      print at_line$; "Index two is out of range:"; index2: errors = true: exit function
    end if
  end if

  ' compute the actual index
  lo = var_names(i).lo_bnd
  if var_names(i).multi then
    lo2 = var_names(i).lo_bnd2
    x = var_names(i).index + (var_names(i).a_width * (ar_scale(index2, lo2) - 1) + ar_scale(index, lo)) - 1
  else
    x = var_names(i).index + ar_scale(index, lo) - 1
    'x = var_names(i).index + index - (var_names(i).lo_bnd - 1) - 1
  end if
  'print "index: "; x

  if tracing then print ident;"(";index;")[";x;"] =";
  get_array_index& = x
end function

' primary: if var does not exist, create it.  Return the var store index
' sym is the numeric variable name
function getvarindex&(side as integer)
  dim i as integer, ident as string, ident_type as integer

  ident = sym: ident_type = symtype
  call getsym

  if ident_type = tystrident then
    print at_line$; "type mismatch": errors = true
  elseif ident_type <> tyident then
    print at_line$; "getvarindex: not a variable": errors = true
  else
    ' see if variable exists
    i = find_vname&(ident)
    if i > 0 then
      getvarindex& = var_names(i).index
      if side = left_side and var_names(i).is_const then print at_line$; "Cannot update const variable: "; ident: errors = true
      exit function
    end if

    'if side = right_side then print at_line$; "Reference to unassigned variable: "; ident: errors = true

    ' create a new variable
    num_store_max = num_store_max + 1
    var_names_max = var_names_max + 1

    var_names(var_names_max).vname   = ident
    var_names(var_names_max).symtype = ident_type
    var_names(var_names_max).index   = num_store_max
    numeric_store(num_store_max)     = 0    ' default value

    getvarindex& = num_store_max
  end if
end function

function getstrindex&(side as integer)
  dim i as integer, ident as string, ident_type as integer

  ident = sym: ident_type = symtype
  call getsym

  if ident_type = tyident then
    print at_line$; "type mismatch": errors = true
  elseif ident_type <> tystrident then
    print at_line$; "getstrindex: not a variable": errors = true
  else
    ' see if variable exists
    i = find_vname&(ident)
    if i > 0 then
      getstrindex& = var_names(i).index
      if side = left_side and var_names(i).is_const then print at_line$; "Cannot update const variable: "; ident: errors = true
      exit function
    end if

    'if side = right_side then print at_line$; "Reference to unassigned variable: "; ident: errors = true

    ' create a new variable
    str_store_max = str_store_max + 1
    var_names_max = var_names_max + 1

    var_names(var_names_max).vname   = ident
    var_names(var_names_max).symtype = ident_type
    var_names(var_names_max).index   = str_store_max
    string_store(str_store_max)      = ""    ' default value

    getstrindex& = str_store_max
  end if
end function

' a(expr)
' when called, sym pointing at the ident
function get_numeric_array_value#
  dim ident as string, ident_type as integer, x as long, n as double

  ident = sym: ident_type = symtype
  x = get_array_index&(ident)
  n = numeric_arr_store(x)
  get_numeric_array_value# = n
end function

' a(expr)
' when called, sym pointing at the ident
function get_string_array_value$
  dim ident as string, ident_type as integer, x as long, s as string

  ident = sym: ident_type = symtype
  x = get_array_index&(ident)
  s = string_arr_store(x)
  get_string_array_value$ = s
end function

sub stridstmt
  dim i as integer, vname as string

  vname = sym
  'print "stridstmt"
  i = getstrindex&(left_side)
  expect("=")
  string_store(i) = strexpression$
  if tracing then print vname, string_store(i)
end sub

sub idstmt
  dim i as integer, vname as string

  vname = sym
  i = getvarindex&(left_side)
  expect("=")
  numeric_store(i) = numeric_expr#
  if tracing then print "*** "; vname, " = "; numeric_store(i)
end sub

' ident = expression
sub assignment
  if symtype = tyident then
    call idstmt
  elseif symtype = tystrident then
    call stridstmt
  else
    print at_line$; "Expecting assignment stmt, found: "; sym: errors = true
  end if
end sub

' ident(expression [, expression]) = expression
sub array_assignment
  dim ident as string, ident_type as integer
  dim s as string, n as double, x as long

  ident = sym: ident_type = symtype
  x = get_array_index&(ident)

  expect("=")

  if ident_type = tystrident then
    s = strexpression$
    'assign string
    string_arr_store(x) = s
    if tracing then print s
  else
    n = numeric_expr#
    'assign number
    numeric_arr_store(x) = n
    if tracing then print n
  end if
end sub

' array assignment: @(expr) = expr
sub atassn
  dim atndx, n as long

  expect("(")
  atndx = numeric_expr#
  expect(")")

  expect("=")

  n = numeric_expr#
  atarray(atndx) = n
  if tracing then print "*** @("; atndx; ") = "; n
end sub

'------------------------------------------------------------------------
' statement parsing
'------------------------------------------------------------------------

sub showhelp
  print "bye or quit -- exit"
  print "help        -- show this screen"
  print "clear       -- clear variables"
  print "edit        -- edit current program"
  print "list        -- show source"
  print "list vars   -- show variables"
  print "load        -- load program from disk"
  print "new         -- clear program in memory"
  print "reload      -- reload program from disk"
  print "run         -- run program in memory"
  print "save        -- save program to disk"
  print ""
  print "cls         -- clear screen"
  print "tron        -- tracing on"
  print "troff       -- tracing off"
  print "ston        -- stepping on"
  print "stoff       -- stepping off"
end sub

function getfn$(prompt as string)
  dim filespec as string
  if symtype = tystring or symtype = tystrident then
    filespec = strexpression$
  elseif sym <> "" then
    filespec = sym                 ' gettoeol destroys sym
    filespec = filespec + gettoeol$
  else
    print prompt; ": ";
    line input filespec
  end if
  if filespec <> "" then
    if instr(filespec, ".") = 0 then filespec = filespec + ".bas"
  end if
  getfn$ = filespec
end function

sub clearvars
  dim i as integer

  for i = 1 to str_store_max
    string_store(i) = ""
  next

  for i = 1 to num_store_max
    numeric_store(i) = 0
  next
end sub

sub initvars
  dim i as integer

  clearvars
  for i = 1 to var_names_max
    var_names(i).vname = ""
    var_names(i).index = 0
  next

  str_store_max = 0: num_store_max = 0: var_names_max = 0
end sub

sub loadprog(fname as string)
  dim n as integer, f as long
  initvars
  clearprog

  if fname = "" then curr_filename = getfn$("Program file") else curr_filename = fname
  if curr_filename = "" then exit sub
  if instr(curr_filename, ".") = 0 then curr_filename = curr_filename + ".bas"
  if not fileexists%(curr_filename) then
    print at_line$; "File "; curr_filename; " not found": errors = true
    exit sub
  end if
  f = freefile
  open curr_filename for input as #f

  n = 0
  while not eof(f)
    line input #f, pgm(0)
    call initgetsym(0, 1)
    if symtype = tynum and the_num > 0 and the_num <= pgmsize then
      n = the_num
    else
      n = n + 1: textp = 1
    end if
    if pgm(n) <> "" then
      dim s as string
      print "line "; n; " is being overwritten, continue (y/n)": line input s
      if s <> s then exit while
    end if
    pgm(n) = mid$(pgm(0), textp)
  wend

  close #f
  curline = 0
end sub

sub editstmt
  dim editor as string
  editor = environ$("EDITOR")
  if editor = "" then editor = "notepad.exe"
  if curr_filename = "" then curr_filename = "default.bas"
  shell editor + " " + curr_filename
  call loadprog(curr_filename)
end sub


'    DIM ff AS INTEGER, l$
'    ff = FREEFILE
'    OPEN file$ FOR BINARY AS ff
'
'    currentLine = 0
'    DO
'        IF EOF(ff) THEN EXIT DO
'        LINE INPUT #ff, l$
'        currentLine = currentLine + 1
'        IF currentLine > UBOUND(program) THEN REDIM _PRESERVE program(currentLine + 999) AS STRING
'        program(currentLine) = l$
'    LOOP
'
'    CLOSE ff
' open filename for input as [#]1
sub openstmt
  dim fname as string, b as integer

  fname = strexpression$
  expect("for")
  expect("input")
  expect("as")
  b = accept("#")
  if symtype <> tynum then
    print at_line$; "file number expected, found: "; sym: errors = true
    call getsym
    exit sub
  end if
  call getsym
  if not fileexists%(fname) then
    print at_line$; "File "; fname; " not found": errors = true
    exit sub
  end if

  filenum = freefile
  open fname for input as #filenum
end sub

' close [#] number
sub closestmt
  dim b as integer

  b = accept("#")
  if symtype <> tynum then
    print at_line$; "file number expected, found: "; sym: errors = true
    call getsym
    exit sub
  end if
  call getsym
  close #filenum
end sub

' eof([#]number)
function eoff%
  dim b as integer

  expect("(")
  b = accept("#")
  if symtype <> tynum then
    print at_line$; "file number expected, found: "; sym: errors = true
    call getsym
    exit function
  end if
  call getsym
  expect(")")
  eoff% = eof(filenum)
end function

' line input #1, st$
' # has been parsed, pointing to
sub fileinput
  dim st as string, i as long, x as long, ident as string, ident_type as integer

  if symtype <> tynum then
    print at_line$; "file number expected, found: "; sym: errors = true
    call getsym
    exit sub
  end if
  call getsym
  expect(",")
  ident = sym: ident_type = symtype
  if ident_type <> tystrident then print at_line$; "String variable expected": errors = true: exit sub
  line input #filenum, st

  i = find_vname&(ident)
  if i > 0 then
    if ident_type <> var_names(i).symtype then
      print at_line$; "Type mismatch: "; ident_type; " vs. table: "; var_names(i).symtype: errors = true: exit sub
    end if
    if var_names(i).a_len > 0 then ' array
      x = get_array_index&(ident)

      'assign string
      string_arr_store(x) = st
      if tracing then print st

      exit sub

    end if
  end if

  i = getstrindex&(left_side)
  string_store(i) = st
end sub

sub runprog
  if sym <> "" then call loadprog("")
  call initgetsym(1, 1)
end sub

sub saveprog
  dim filespec as string
  dim i as integer
  filespec = getfn$("Save as")
  if filespec = "" then exit sub
  open filespec for output as 1
  if err = 8 then
     print at_line$; "*** error: you don't have permission to write to that file."
     exit sub
  end if
  for i = 1 to pgmsize
    if len(pgm(i)) then print #1, i; " "; pgm(i)
  next
  close #1
end sub

sub liststmt
  dim i as integer
  if sym = "vars" then
    for i = 1 to var_names_max
      if var_names(i).a_len > 0 then
          print "Array:"; var_names(i).vname, " index: "; var_names(i).index;
          print string_store(var_names(i).index); " size: "; var_names(i).a_len;
          print " type: "; var_names(i).symtype
      elseif right$(var_names(i).vname, 1) = "$" then
          print "String:"; var_names(i).vname, " index: "; var_names(i).index;
          print string_store(var_names(i).index);
          print " type: "; var_names(i).symtype
      elseif var_names(i).vname <> "" then
          print "Number:"; var_names(i).vname, " index: "; var_names(i).index;
          print numeric_store(var_names(i).index);
          print " type: "; var_names(i).symtype
      end if
    next
  else
    for i = 1 to pgmsize
      if pgm(i) <> "" then print i; " "; pgm(i)
    next
  end if
  print
end sub

sub chdircmd
  chdir strexpression$
end sub

' CIRCLE [STEP] (x!,y!),radius![,[color%] [,[start!] [,[end!] [,aspect!]]]]
sub circlestmt
  dim x as single, y as single, radius as single, clr as long
  dim arcbeg as single, arcend as single, elipse as single

  expect("(")
  x = numeric_expr#
  expect(",")
  y = numeric_expr#
  expect(")")
  expect(",")
  radius = numeric_expr#

  '[,[color%] [,[start!] [,[end!] [,aspect!]]]]
  if accept&(",") then           ' color
    if accept&(",") then         ' arcbeg
      if accept&(",") then       ' arcend
        if accept&(",") then     ' elipse
          elipse = numeric_expr#
          circle (x, y), radius, , , , elipse
        else
          arcend = numeric_expr#
          if accept&(",") then
            elipse = numeric_expr#
            circle (x, y), radius, , , arcend, elipse
          else
            circle (x, y), radius, , , arcend
          end if
        end if
      else
        arcbeg = numeric_expr#
        if accept&(",") then       ' arcend
          if accept&(",") then     ' elipse
            elipse = numeric_expr#
            circle (x, y), radius, , arcbeg, , elipse
          else
            arcend = numeric_expr#
            if accept&(",") then
              elipse = numeric_expr#
              circle (x, y), radius, , arcbeg, arcend, elipse
            else
              circle (x, y), radius, , arcbeg, arcend
            end if
          end if
        end if
      end if
    else
      ' [,[start!] [,[end!] [,aspect!]]]]
      clr = numeric_expr#
      if accept&(",") then         ' arcbeg
        if accept&(",") then       ' arcend
          if accept&(",") then     ' elipse
            elipse = numeric_expr#
            circle (x, y), radius, clr, , , elipse
          else
            arcend = numeric_expr#
            if accept&(",") then
              elipse = numeric_expr#
              circle (x, y), radius, clr, , arcend, elipse
            else
              circle (x, y), radius, clr, , arcend
            end if
          end if
        else
          arcbeg = numeric_expr#
          if accept&(",") then       ' arcend
            if accept&(",") then     ' elipse
              elipse = numeric_expr#
              circle (x, y), radius, clr, arcbeg, , elipse
            else
              arcend = numeric_expr#
              if accept&(",") then
                elipse = numeric_expr#
                circle (x, y), radius, clr, arcbeg, arcend, elipse
              else
                circle (x, y), radius, clr, arcbeg, arcend
              end if
            end if
          else
            circle (x, y), radius, clr, arcbeg
          end if
        end if
      else
        circle (x, y), radius, clr
      end if
    end if
  else
    circle (x, y), radius
  end if
end sub

' color [fore] [,back]
sub colorstmt
  dim back as long, fore as long
  if accept&(",") then
    back = numeric_expr#
    color , back
  else
    fore = numeric_expr#
    if accept&(",") then
      back = numeric_expr#
      color fore, back
    else
      color fore
    end if
  end if
end sub

sub get_array_bounds(lo as long, hi as long)
    lo = numeric_expr#
    if accept&("to") then
      hi = numeric_expr#
    else
      hi = lo
      lo = 0
    end if
end sub

' dim ident(numeric expression [to numeric expression]) {, ident(numeric expression [to numeric expression])}
sub dimstmt
  dim ident as string, ident_type as integer, lo as long, hi as long, lo2 as long, hi2 as long
  dim a_len as long, index as long, i as integer, multi as integer, a_width as long

  do
    ident = sym
    ident_type = symtype
    if symtype <> tyident and symtype <> tystrident then
      print at_line$; " Expecting an identifier, but found: "; sym: errors = true: exit sub
    end if
    call getsym   ' skip array name

    expect("(")
    call get_array_bounds(lo, hi)
    lo2 = 0: hi2 = 0: multi = false
    if accept&(",") then call get_array_bounds(lo2, hi2): multi = true
    expect(")")

    ' see if it already exists
    i = find_vname&(ident)
    if i > 0 then print "Duplicate definition: "; ident: errors = true: exit sub

    ' add it
    a_len = hi - lo + 1
    if multi then
        a_width = a_len
        a_len = a_len * (hi2 - lo2 + 1)
    end if

    var_names_max = var_names_max + 1
    var_names(var_names_max).vname   = ident
    var_names(var_names_max).symtype = ident_type
    var_names(var_names_max).lo_bnd  = lo
    var_names(var_names_max).hi_bnd  = hi
    var_names(var_names_max).lo_bnd2 = lo2
    var_names(var_names_max).hi_bnd2 = hi2
    var_names(var_names_max).multi   = multi
    var_names(var_names_max).a_len   = a_len
    var_names(var_names_max).a_width = a_width

    if ident_type = tystrident then
      index = str_arr_stor_max + 1
      str_arr_stor_max = str_arr_stor_max + a_len
      redim preserve string_arr_store(str_arr_stor_max)
    else
      index = num_arr_stor_max + 1
      num_arr_stor_max = num_arr_stor_max + a_len
      redim preserve numeric_arr_store(num_arr_stor_max)
    end if

    var_names(var_names_max).index = index

    if sym <> "," then exit do
    call getsym
  loop
end sub

' const id[$] = number|string {, const id[$] = number|string}
sub conststmt
  dim i as integer

  do
    i = find_vname&(sym)
    if i <> 0 then print at_line$; "var: "; sym; " already defined": errors = true: exit sub
    call assignment
    var_names(var_names_max).is_const = true
  loop while accept&(",")

end sub

sub drawstmt
  dim s as string
  s = strexpression$
  draw s
end sub

sub environstmt
  setenviron strexpression$
end sub

' need to account for loop [until|while expr] and next [i]
sub exitstmt
  if sym = "while" then
    call getsym
    if while_sp <= 0 then errors = true: print at_line$; "'exit while' without while": errors = true: exit sub
    while_sp = while_sp - 1
    call find_matching_pair("while", "wend")
    call getsym
  elseif sym = "do" then
    call getsym
    if do_sp <= 0 then errors = true: print at_line$; "'exit do' without do": errors = true: exit sub
    do_sp = do_sp - 1
    call find_matching_pair("do", "loop")
    call getsym
    if sym = "until" or sym = "while" then
      call getsym   ' skip until\while
      ' somehow skip over the until\while expression
      while sym <> ":" and sym <> ""
        call getsym
      wend
    end if
  elseif sym = "for" then
    call getsym
    if loopp <= 0 then errors = true: print at_line$; "'exit for' without do": errors = true: exit sub
    loopp = loopp - 1
    call find_matching_pair("for", "next")
    call getsym
    if symtype = tyident then call getsym
  else
    print at_line$; "'exit without do/for/while": errors = true: exit sub
  end if

  if endif_count > 0 and if_sp    > 0 then if_sp    = if_sp    - endif_count
  if loop_count  > 0 and do_sp    > 0 then do_sp    = do_sp    - loop_count
  if next_count  > 0 and loopp    > 0 then loopp    = loopp    - next_count
  if wend_count  > 0 and while_sp > 0 then while_sp = while_sp - wend_count

end sub

' for xvar = -1.5 to 1.5 step .01
sub forstmt
  dim xvar as integer, i as integer, fori as double, forto as double

  xvar = getvarindex&(left_side)   ' get position of "i"
  if loopp >= 0 then
    for i = 0 to loopp - 1
      if loopvars(i) = xvar then
        print at_line$; "for index variable already in use": errors = true
        exit sub
      end if
    next
  end if
  expect("=")
  fori = numeric_expr#
  expect("to")
  forto = numeric_expr#
  if fori > forto then
    call find_matching_pair("for", "next")
    call getsym
    if symtype = tyident then call getsym
  else
    numeric_store(xvar) = fori
    loopp = loopp + 1
    loopvars(loopp) = xvar
    looplines(loopp) = curline
    loopmax(loopp) = forto

    if accept&("step") then loopstep(loopp) = numeric_expr# else loopstep(loopp) = 1
    loopoff(loopp) = textp
    if len(sym) > 0 then loopoff(loopp) = textp - len(sym) - 1
  end if
end sub

' finds target, using current sym
' bug fix: if numeric target, save and restore textp.
function get_target&
  dim save_textp
  if symtype = tynum then
    save_textp = textp
    get_target = numeric_expr#
    textp = save_textp
  else
    dim i as integer, lbl as string
    lbl = sym
    if right$(lbl, 1) <> ":" then lbl = lbl + ":"
    for i = 1 to pgmsize
      if lcase$(mid$(ltrim$(pgm(i)), 1, len(lbl))) = lbl then
        get_target& = i
        exit function
      end if
    next
    print at_line$; "Target of goto not found:"; sym: errors = true
    get_target& = 0
  end if
end function

sub gosubstmt
  dim target as integer

  target = get_target&
  if not errors then
    validlinenum(target)
    stackp = stackp + 1
    if stackp > stacksize then print at_line$; "out of stack space": errors = true
    gosubstack(stackp) = curline
    ' 26 May 2021 was just textp
    gosuboffstack(stackp) = textp - 1
    'print "[ "; curline; " ]"; "textp:"; textp; "=>"; pgm$(curline)
    'if sym = ":" then gosuboffstack(stackp) = textp
    call initgetsym(target, 1)
  end if
end sub

sub gotostmt
  dim target as integer

  target = get_target&
  gotoline(target)
end sub

' single line if: if expr then if expr then if expr then s else s else s else s
sub ifstmt
  dim b as integer, level as integer, cond as integer

  level = 0

  begin:

  level = level + 1
  cond = numeric_expr#
  b = accept&("then")
  '*** multiline if processing ***
  if sym = "" then  'multiline if
    if level > 1 then
      print at_line$; "can't mix multi and single line 'if'": errors = true
      exit sub
    end if
    call multi_ifstmt(cond)
  '*** singleline if processing ***
  elseif cond then
    if symtype = tynum then
        gotoline(int(the_num))
    elseif accept&("if") then
        goto begin
    end if
  else
    call find_matching_sline_if
    ' if else found, pick up there, otherwise skip rest of stmt
    if not accept&("else") then skiptoeol
    if symtype = tynum then gotoline(int(the_num))
  end if
end sub

sub multi_ifstmt(cond as integer)
  dim s as string, b as integer

  if_sp = if_sp + 1
  if_stack(if_sp) = curline
  'print at_line$; "if after inc: if_sp: "; if_sp, pgm(curline)

  if cond then
    rem let docmd process these commands
  else
    'need to find the next corresponding 'elseif' or 'else' or 'endif'
    restart:
    ' on the "if" or "elseif" line, so skip it
    s = find_matching_else$ 'either elseif, else or endif
    'print at_line$; "found: "; sym
    if s = "" then print at_line$; "missing endif": errors = true: exit sub
    if tracing then print "["; curline; "] "; sym; " "; mid$(thelin, textp)
    if sym = "elseif" then
      'print sym; ": "; mid$(thelin, textp)
      call getsym 'skip "elseif"
      cond = numeric_expr#
      b = accept&("then")
      'print at_line$; "elseif evaluated to: "; cond
      if cond then
        rem let docmd process these commands, until next elseif/else/endif
      else
        goto restart
      end if
    elseif sym = "else" then
      rem - let docmd process these commands, until endif
      call getsym   ' skip the else, so docmd goes to next line
    elseif sym = "endif" then
      call endifstmt
    end if
  end if
end sub

' called from docmd()
sub elseifstmt
  dim s as string

  if if_sp = 0 then print at_line$; "endif without if": errors = true: exit sub

  'scan until matching endif

  ' but first, allow more "elseif"'s
  do
    s = find_matching_else$
  loop while s = "elseif"

  ' allow an "else"
  if s = "else" then
    s = find_matching_else$
  end if

  ' finally, need an "endif"
  if s = "endif" then
    ' pop the if stack
    if_sp = if_sp - 1
    call getsym  ' skip "endif"
    ' done
  else
    print at_line$; "Missing endif": errors = true: exit sub
  end if
end sub

' called from docmd()
sub elsestmt
  'print at_line$; "else begin: if_sp: "; if_sp, pgm(curline)

  'part of a single-line if?
  call initgetsym(curline, 1)
  'if not "else", then single-line if
  if sym <> "else" then call skiptoeol: exit sub

  ' looks like multiline if - but have we seen the start of it?
  if if_sp = 0 then print at_line$; "else without if": errors = true: exit sub

  'scan until matching endif
  if find_matching_else$ <> "endif" then print at_line$; "else without endif": errors = true: exit sub

  call getsym 'skip the "endif"
  'pop the if stack
  if_sp = if_sp - 1
  'print at_line$; "else end: if_sp: "; if_sp, pgm(curline)
end sub

' called from docmd()
sub endifstmt
  if if_sp = 0 then print at_line$; "endif without if": errors = true: exit sub
  if_sp = if_sp - 1
  'print at_line$; "endif: if_sp: "; if_sp, pgm(curline)
  call getsym 'skip "endif"
end sub

' input [;] ["prompt" ;|,] variablelist
sub inputsetup
  if left$(sym, 1) = chr$(34) then
    print mid$(sym, 2, len(sym) - 1);
    call getsym
    if accept&(";") then
      print "? ";
    else
      expect(",")
    end if
  end if
end sub

' input [;] ["prompt" ;|,] variablelist
sub inputstmt
  dim ident as string, ident_type as integer, i as long, x as long, st as string, n as double

  inputsetup

  ident = sym: ident_type = symtype
  if ident_type = tystrident then
    input "", st
  else
    line input st
    if st = "" then st = "0"
    if left$(st, 1) >= "0" and left$(st, 1) <= "9" then
      n = val(st)
    else
      n = asc(st)
    end if
  end if

  i = find_vname&(ident)
  if i > 0 then
    if ident_type <> var_names(i).symtype then
      print at_line$; "Type mismatch: "; ident_type; " vs. table: "; var_names(i).symtype: errors = true: exit sub
    end if
    if var_names(i).a_len > 0 then ' array
      x = get_array_index&(ident)

      if ident_type = tystrident then
        'assign string
        string_arr_store(x) = st
        if tracing then print st
      else
        'assign number
        numeric_arr_store(x) = n
        if tracing then print n
      end if

      exit sub

    end if
  end if

  if ident_type = tystrident then
    i = getstrindex&(left_side)
    string_store(i) = st
  elseif ident_type = tyident then
    i = getvarindex&(left_side)
    numeric_store(i) = n
  else
    print at_line$; "Unknown type": errors = true: exit sub
  end if
end sub

' line input [;] ["prompt";] variable$
' line input #1, st$
sub lineinputstmt
  dim ident as string, ident_type as integer, i as long, x as long, st as string

  if not accept&("input") then linestmt: exit sub
  if accept("#") then fileinput: exit sub
  inputsetup

  ident = sym: ident_type = symtype

  if ident_type <> tystrident then print at_line$; "String variable expected": errors = true: exit sub
  line input st

  i = find_vname&(ident)
  if i > 0 then
    if ident_type <> var_names(i).symtype then
      print at_line$; "Type mismatch: "; ident_type; " vs. table: "; var_names(i).symtype: errors = true: exit sub
    end if
    if var_names(i).a_len > 0 then ' array
      x = get_array_index&(ident)

      'assign string
      string_arr_store(x) = st
      if tracing then print st

      exit sub

    end if
  end if

  i = getstrindex&(left_side)
  string_store(i) = st
end sub

' line [[step](x1!,y1!)]-[step](x2!,y2!) [,[color%] [,[b | bf] [,style%]]]
' line -(xz,yz)[,numeric expr]
' ??? step is not currently supported
sub linestmt
  dim x1 as single, y1 as single, x2 as single, y2 as single, clr as long
  dim rect_type as string, step1 as integer, step2 as integer

  step1 = false: step2 = false

  if accept&("-") then
    expect("(")
    x1 = numeric_expr#
    expect(",")
    y1 = numeric_expr#
    expect(")")
    if accept&(",") then
      clr = numeric_expr#
      line -(x1, y1), clr
    else
      line -(x1, y1)
    end if
    exit sub
  end if

  if accept&("step") then step1 = true
  expect("(")
  x1 = numeric_expr#
  expect(",")
  y1 = numeric_expr#
  expect(")")

  expect("-")
  if accept&("step") then step2 = true

  expect("(")
  x2 = numeric_expr#
  expect(",")
  y2 = numeric_expr#
  expect(")")

  ' so far we have: line(x, y)-(x2, y2)

  if is_stmt_end& then line (x1, y1)-(x2, y2): exit sub

  '[,[color%] [,[b | bf] [,style%]]]
  ' only acceptable value is a ","

  '1) ,c
  '2) ,c,b
  '3) ,c,b,s
  '4) ,c,,s
  '5) ,,b
  '6) ,,b,s
  '7) ,,,s

  if accept&(",") then
    if accept&(",") then
      if accept&(",") then
        'must have s (7)
        line (x1, y1)-(x2, y2), , , numeric_expr#
      else
        'must have b
        rect_type = ucase$(sym)
        if rect_type <> "B" and rect_type <> "BF" then
          print at_line$; "line ... - expecting 'B' or 'BF', found: "; rect_type: errors = true: exit sub
        end if
        if accept&(",") then
          'must have s (6)
          if rect_type = "B" then
            line (x1, y1)-(x2, y2), , B, numeric_expr#
          else
            line (x1, y1)-(x2, y2), , BF, numeric_expr#
          end if
        else
          '(5)
          if rect_type = "B" then
            line (x1, y1)-(x2, y2), , B
          else
            line (x1, y1)-(x2, y2), , BF
          end if
          call getsym ' skip "B"
        end if
      end if
    else
      'must have c
      clr = numeric_expr#
      if accept&(",") then
        if accept&(",") then
          'must have s (4)
          line (x1, y1)-(x2, y2), clr, , numeric_expr#
        else
          'must have b
          rect_type = ucase$(sym)
          if rect_type <> "B" and rect_type <> "BF" then
            print at_line$; "line ... - expecting 'B' or 'BF', found: "; rect_type: errors = true: exit sub
          end if
          if accept&(",") then
            'must have s (3)
            if rect_type = "B" then
              line (x1, y1)-(x2, y2), clr , B, numeric_expr#
            else
              line (x1, y1)-(x2, y2), clr, BF, numeric_expr#
            end if
          else
            '(2)
            if rect_type = "B" then
              line (x1, y1)-(x2, y2), clr, B
            else
              line (x1, y1)-(x2, y2), clr, BF
            end if
            call getsym ' skip "B"
          end if
        end if
      else
        '(1)
        line (x1, y1)-(x2, y2), clr
      end if
    end if
  end if
end sub

sub locatestmt
  dim row as integer, col as integer
  if accept&(",") then
    col = numeric_expr#
    locate , col
  else
    row = numeric_expr#
    if accept&(",") then
      col = numeric_expr#
      locate row, col
    else
      locate row
    end if
  end if
end sub

' mid$(s, i, n)
sub midstmt
  dim xvar as integer, start as integer, length as integer, nolength as integer
  expect("(")
  xvar = getstrindex&(left_side)
  expect(",")
  start = numeric_expr#
  if accept&(",") then length = numeric_expr# else nolength = -1
  expect(")")
  expect("=")
  if nolength then
    mid$(string_store(xvar), start) = strexpression$
  else
    mid$(string_store(xvar), start, length) = strexpression$
  end if
end sub

sub nextstmt
  dim cont as integer

  if symtype = tyident then call getsym
  if loopp < 0 then print at_line$; "next without for": errors = true: exit sub
  ' increment the current "i"
  numeric_store(loopvars(loopp)) = numeric_store(loopvars(loopp)) + loopstep(loopp)
  if tracing then print "["; curline; "] "; "next: "; numeric_store(loopvars(loopp))

  ' see if "for" should continue
  cont = false
  if loopstep(loopp) < 0 then
    if numeric_store(loopvars(loopp)) >= loopmax(loopp) then
      cont = true
    end if
  else
    if numeric_store(loopvars(loopp)) <= loopmax(loopp) then
      cont = true
    end if
  end if

  if cont then
    call initgetsym(looplines(loopp), loopoff(loopp))
  else
    loopp = loopp - 1
  end if

end sub

' PAINT [STEP] (column%, row%), fillColor[, borderColor%]
sub paintstmt
  dim x as long, y as long, f as long

  expect("(")
  x = numeric_expr#
  expect(",")
  y = numeric_expr#
  expect(")")
  if accept&(",") then
    if accept&(",") then
      paint (x, y), , numeric_expr#
    else
      f = numeric_expr#
      if accept&(",") then
        paint (x, y), f, numeric_expr#
      else
        paint (x, y), f
      end if
    end if
  else
    paint (x, y)
  end if
end sub

' palette [attribute%,color&]
sub palettestmt
    dim a as integer, c as long

    a = numeric_expr#
    expect(",")
    c = numeric_expr#
    palette a, c
end sub

sub printstmt
  dim val_type, printnl, printwidth as integer, n as long, junk as string

  printnl = true
  if accept&(",") then print ,
  do while sym <> "" and sym <> ":" and sym <> "else"
    printwidth = 0

    if accept("#") then
      if symtype = tynum then
        printwidth = the_num
      end if
      call getsym
      expect(",")
      val_type = any_expr(0)
      if val_type = tystring then
        junk = pop_str
      else
        n = pop_num
        junk = ltrim$(str$(n))
      end if
      printwidth = printwidth - len(junk)
      if printwidth <= 0 then print junk; else print space$(printwidth); junk;
      if accept(",") or accept(";") then printnl = false else printnl = true: exit do
    else
      val_type = any_expr&(0)
      if val_type = tystring then
        junk = pop_str
      else
        junk = ltrim$(str$(pop_num))
      end if

      if accept&(",") then
        print junk,
        printnl = false
      elseif accept&(";") then
        print junk;
        printnl = false
      else
        print junk
        printnl = false
        exit do
      end if
    end if
  loop
  if printnl then print
end sub

' preset   (column, row)
' preset [step] (x!,y!) [,color%]
sub presetstmt
  dim x as single, y as single
  expect("(")
  x = numeric_expr#
  expect(",")
  y = numeric_expr#
  expect(")")
  if accept&(",") then preset (x, y), numeric_expr# else preset (x, y)
end sub

' pset   (column, row)
' pset [step] (x!,y!) [,color%]
' PSET [STEP] (x!,y!) [,color%]
sub psetstmt
  dim x as single, y as single, clr as long
  expect("(")
  x = numeric_expr#
  expect(",")
  y = numeric_expr#
  expect(")")
  if accept&(",") then
    clr = numeric_expr#
    pset (x, y), clr
  else
    pset (x, y)
  end if
end sub

sub randomizer
  if sym = "" then randomize timer else randomize numeric_expr#
end sub

sub returnstmt
  dim lin as integer, offs as integer
  if stackp < 0 then print at_line$; "return without gosub": errors = true: exit sub
  lin = gosubstack(stackp)
  offs = gosuboffstack(stackp)
  if tracing then print "returning to: "; lin; ": "; offs
  'print "["; curline; "] "; "returning to: "; lin; ": "; offs; " while_sp: "; while_sp
  stackp = stackp - 1
  if offs <= 1 then print at_line$; "returnstmt - offs <= 1": errors = true
  call initgetsym(lin, offs)
end sub

' Screen [ mode ] [, [ colormode ] [, [ active_page ] [, [ visible_page ]]]]
sub screenstmt
  dim a, b, c, d as long

  if accept&(",") then
    if accept&(",") then
      c = numeric_expr#
      d = numeric_expr#
      screen , , c, d
    end if
  else
    a = numeric_expr#
    if accept&(",") then
      b = numeric_expr#
      if accept&(",") then
        c = numeric_expr#
        if accept&(",") then
          d = numeric_expr#
          screen a, b, c, d
        end if
      end if
    else
      screen a
    end if
  end if
end sub

' shell [string]
sub shellstmt
  dim s as string

  s = ""
  while the_ch <> "" and the_ch <> ":"
    s = s + the_ch
    call getch
  wend

  shell s
  'print "shell: "; s
  call skiptoeol
end sub

' sleep [seconds]
sub sleepstmt
  if is_stmt_end& then sleep else sleep numeric_expr#
end sub

' swap v1, v2
sub swapstmt
  dim i1 as integer, i2 as integer
  dim symtype1 as integer, symtype2 as integer
  dim sym1 as string, sym2 as string

  sym1     = sym
  symtype1 = symtype
  if symtype = tyident then
    i1 = getvarindex&(left_side)
  else
    i1 = getstrindex&(left_side)
  end if

  expect(",")

  sym2     = sym
  symtype2 = symtype

  if symtype = tyident then
    i2 = getvarindex&(left_side)
  else
    i2 = getstrindex&(left_side)
  end if

  if symtype1 <> symtype2 then
    print at_line$; sym1; " and "; sym2; " are not the same data type": errors = true
    exit sub
  end if

  if symtype1 = tyident then
    swap numeric_store(i1), numeric_store(i2)
  else
    swap string_store(i1), string_store(i2)
  end if
end sub

' VIEW [[SCREEN] (x1!,y1!)-(x2!,y2!) [,[color%] [,border%]]]
sub viewstmt
  dim x1 as long, y1 as long, x2 as long, y2 as long, clr as long, border as long

  expect("(")
  x1 = numeric_expr#
  expect(",")
  y1 = numeric_expr#
  expect(")")

  expect("-")

  expect("(")
  x2 = numeric_expr#
  expect(",")
  y2 = numeric_expr#
  expect(")")

  if accept&(",") then
    if accept&(",") then
      border = numeric_expr#
      view (x1, y1)-(x2, y2), , border
    else
      clr = numeric_expr#
      if accept&(",") then
        border = numeric_expr#
        view (x1, y1)-(x2, y2), clr, border
      else
        view (x1, y1)-(x2, y2), clr
      end if
    end if
  else
    view (x1, y1)-(x2, y2)
  end if
end sub

sub whilestmt(first as integer)
  if first then
    while_sp = while_sp + 1
    while_line(while_sp) = curline
    while_off(while_sp) = textp
    if len(sym) > 0 then while_off(while_sp) = textp - len(sym) - 1
  end if
  'print "["; curline; "] "; "*while:sym:";sym; " textp:";textp; " =>";mid$(pgm(curline), textp); " while_sp: "; while_sp
  if not bool_expr& then
    while_sp = while_sp - 1
    'print "["; curline; "] "; "*wend bool_expr is 0!"; " while_sp: "; while_sp
    call find_matching_pair("while", "wend")
    call getsym
  end if
end sub

sub wendstmt
  if while_sp <= 0 then errors = true: print at_line$; "wend without while": errors = true: exit sub
  call initgetsym(while_line(while_sp), while_off(while_sp))
  if tracing then print "["; curline; "] "; "wend"
  whilestmt(false)
end sub

' do [(while|until) expr][:]
sub dostmt(first as integer)
  if first then
    do_sp = do_sp + 1
    do_loop(do_sp).lline = curline

    do_loop(do_sp).loff = textp
    if len(sym) > 0 then do_loop(do_sp).loff = textp - len(sym) - 1
    'print "*do:"; "sym:"; sym; " textp:";textp; "=>";mid$(pgm(curline), textp - len(sym))
  end if

  if sym = "while" then
    call getsym
    if not bool_expr& then
      do_sp = do_sp - 1
      call find_matching_pair("do", "loop")
      call getsym
    end if
  elseif sym = "until" then
    call getsym
    if bool_expr& then
      do_sp = do_sp - 1
      call find_matching_pair("do", "loop")
      call getsym
    end if
  end if
end sub

' loop [(while|until) expr]
sub loopstmt
  if do_sp <= 0 then errors = true: print at_line$; "loop without do": errors = true: exit sub

  if sym = "while" then
    call getsym
    if not bool_expr& then
      do_sp = do_sp - 1
      exit sub
    end if
  elseif sym = "until" then
    call getsym
    if bool_expr& then
      do_sp = do_sp - 1
      exit sub
    end if
  end if

  call initgetsym(do_loop(do_sp).lline, do_loop(do_sp).loff)
  'print "loop line:"; curline; "off:"; do_loop(do_sp).loff; "==>"; pgm(curline)
  dostmt(false)
end sub

' width , height
' width width
' width width, height
sub widthstmt
  dim w as integer

  if accept&(",") then
    width , numeric_expr#
  else
    w = numeric_expr#
    if accept&(",") then
      width w , numeric_expr#
    else
      width w
    end if
  end if
end sub

' window [ [ screen] (x1!, y1!) - (x2!, y2!)]
sub windowstmt
    dim x1 as single, y1 as single, x2 as single, y2 as single

    if sym = "" then window: exit sub

    expect("(")
    x1 = numeric_expr#
    expect(",")
    y1 = numeric_expr#
    expect(")")

    expect("-")

    expect("(")
    x2 = numeric_expr#
    expect(",")
    y2 = numeric_expr#
    expect(")")

    window (x1, y1) - (x2, y2)
end sub

'------------------------------------------------------------------------
'  Various helper routines
'------------------------------------------------------------------------

sub skip_exit
    call getsym
    if sym = "do" or sym = "while" or sym = "for" then
        call getsym
    end if
end sub

sub find_matching_pair(s1 as string, s2 as string)
  dim level as integer
  dim more as integer
  dim have_sym as integer

  level = 1
  more = true
  have_sym = false

  endif_count = 0: wend_count = 0: next_count = 0: loop_count = 0

  do
    if sym = "exit" then
        call skip_exit
    elseif not have_sym then
        call getsym
        if sym = "exit" then call skip_exit
    end if

    have_sym = false
    'print at_line$; "matching, level"; level; "sym=>"; sym
    'if isalpha&(mid$(sym, 1, 1)) then print "fm: level: sym: "; level; ": '"; sym; "'  "; mid$(thelin, textp, 40)

    select case sym
        case s1: level = level + 1
        case s2: level = level - 1
    end select

    if level = 0 then exit do

    select case sym
        case "if"     ' need to only do "if" case if multiline if
          do
            call getsym
          loop until sym = "then" or sym = ""
          call getsym ' skip the "then"
          ' if nothing past "then", it is a multiline if
          if sym = "" then endif_count = endif_count - 1
        case "endif": endif_count = endif_count + 1
        case "while": wend_count  = wend_count  - 1
        case "wend":  wend_count  = wend_count  + 1
        case "for":   next_count  = next_count  - 1
        case "next":  next_count  = next_count  + 1
        case "do"
          loop_count  = loop_count  - 1
          if sym = "while" then call getsym
        case "loop"
          loop_count  = loop_count  + 1
          if sym = "while" then call getsym
    end select

    if sym = "" then
      if not more then exit sub
      while sym = "" and curline > 0 and curline < pgmsize
        call initgetsym(curline + 1, 1)
      wend
      if sym = "" then
        print at_line$; "Cannot find matching: "; s2: errors = true
        exit sub
      end if
      have_sym = true
    end if
  loop
end sub

' find matching elseif/else/endif
function find_matching_else$
  dim level as integer

  find_matching_else$ = ""
  level = 0
  do
      call initgetsym(curline + 1, 1)
      'print "find_matching_else: "; curline; " sym: "; sym; " level: "; level; "textp: "; textp; " line:"; thelin
      if curline >= pgmsize then print "searching for endif, found eof": errors = true: exit do
      if is_multi_line_if& then
          level = level + 1
      elseif level = 0 and (sym = "elseif" or sym = "else" or sym = "endif") then
          find_matching_else = sym: exit do
      elseif level > 0 and sym = "endif" then
          level = level - 1
      elseif errors then
          exit do
      endif
  loop
end function

sub find_matching_sline_if
  dim level as integer
  level = 1
  do
    'print "find_matching_sline_if level: "; level; " sym: "; sym
    if sym = "if" then
      level = level + 1
    elseif sym = "else" then
      level = level - 1
    end if
    if level = 0 or sym = "" then exit do
    call getsym
  loop
end sub

function is_multi_line_if&
    is_multi_line_if& = false

    if sym = "if" then
        ' is it single or multi line "if" - ignore single line if's
        do
            call getsym
            if sym = "" then print at_line$; "if missing then" : errors = true: exit do
            if sym = "then" then
                call getsym
                if sym = "" then
                    ' multi line "if"
                    is_multi_line_if& = true
                end if
                exit do
            end if
        loop
    end if
end function

function accept&(s as string)
  accept& = false
  if sym = s then accept& = true: call getsym
end function

sub expect(s as string)
  if not accept&(s) then print at_line$; "expecting "; s; " but found "; sym: errors = true
end sub

function is_stmt_end&
  is_stmt_end& = sym = "" or sym = ":"
end function

sub validlinenum(n as integer)
  if n > 0 and n <= pgmsize then exit sub
  print at_line$; "line number out of range:"; the_num: errors = true
end sub

sub clearprog
  dim i as integer
  for i = 1 to pgmsize
    pgm(i) = ""
  next
end sub

sub gotoline(target as integer)
  validlinenum(target)
  call initgetsym(target, 1)
end sub

'------------------------------------------------------------------------
'------[FreeBasic specific functions]------------------------------------
'------------------------------------------------------------------------

' screenres x, y, depth
'sub screenresstmt
'  dim x as long , y as long, depth as long
'
'  x = numeric_expr#
'  expect(",")
'  y = numeric_expr#
'  expect(",")
'  depth = numeric_expr#
'  screenres x, y, depth
'end sub

'------------------------------------------------------------------------
'  various functions called from primary
'------------------------------------------------------------------------

function sinh#(z as double)
  sinh = (e ^ z - e ^ (-z)) / 2
end function

function tanh#(z as double)
  tanh = (e ^ (2 * z) - 1) / (e ^ (2 * z) + 1)
end function

function acosh#(z as double)
  acosh = log(z + sqr(z + 1) * sqr(z - 1))
end function

function acoth#(z as double)
  acoth = .5 * (log(1 + 1 / z) - log(1 - 1 / z))
end function

function acsch#(z as double)
  acsch = log(sqr(1 + z ^ (-2)) + z ^ (-1))
end function

function asech#(z as double)
  asech = log(sqr(z ^ (-1) - 1) * sqr(z ^ (-1) + 1) + z ^ (-1))
end function

function asin2#(i as double)
  if i = -1 then
    asin2 = -halfpi
  elseif i = 1 then
    asin2 = halfpi
  else
    asin2 = atn(i / sqr(1 - i * i))
  end if
end function

function asinh#(z as double)
  asinh = log(z + sqr(1 + z ^ 2))
end function

function atanh#(z as double)
  atanh = .5 * (log(1 + z) - log(1 - z))
end function

function cosh#(z as double)
  cosh = (e ^ z + e ^ (-z)) / 2
end function

function shlf#(x as double, n as double)
  shlf# = x
  if n >= 0 then shlf# = x * (2 ^ n)
end function

function shrf#(x as double, n as double)
  shrf# = x
  if n >= 0 then shrf# = x \ (2 ^ n)
end function

' ([start,] haystack, needle)
function instrfun&
  dim i as integer, haystack as string, needle as string

  expect("(")
  i = 1
  if symtype = tynum or symtype = tyident then
    i = numeric_expr#
    expect(",")
  end if
  haystack = strexpression$
  expect(",")
  needle = strexpression$
  expect(")")
  instrfun& = instr(i, haystack, needle)
end function

' mid$(s$, start [, end])
function midfun$
  dim i as string, x as integer, y as integer

  expect("(")
  i = strexpression$
  expect(",")
  x = numeric_expr#
  if accept&(",") then
    y = numeric_expr#
    midfun$ = mid$(i, x, y)
  else
    midfun$ = mid$(i, x)
  end if
  expect(")")
end function

' lpad$(s$, padded_len [, pad_string$])
function lpadfun$
  dim s as string, pad_string as string, padded_len as integer
  expect("(")
  s = strexpression$
  expect(",")
  padded_len = numeric_expr#
  pad_string = " "
  if accept&(",") then
    pad_string = strexpression$
  end if
  expect(")")

  lpadfun$ = s
  if len(s) > padded_len then
    lpadfun$ = mid$(s, 1, padded_len)
  else
    lpadfun$ = string$(padded_len - len(s), mid$(pad_string, 1, 1)) + s
  end if
end function

' result = peek(string)
function peekfun#(s as string)
  select case s
    case "for index"         : peekfun# = loopp
    case "do index"          : peekfun# = do_sp
    case "while index"       : peekfun# = while_sp
    case "if index"          : peekfun# = if_sp
    case "gosub index"       : peekfun# = stackp
    case "numeric var total" : peekfun# = num_store_max
    case "string var total"  : peekfun# = str_store_max
    case "variables total"   : peekfun# = var_names_max
    case else                : peekfun# = -1
  end select
end function

'result = Point( coord_x, coord_y [,buffer] )
'result = Point( function_index )
function pointfun#
  dim x as integer

  expect("(")
  x = numeric_expr#
  if accept&(",") then
    pointfun# = point(x, numeric_expr#)
  else
    pointfun# = point(x)
  end if
  expect(")")
end function

function posfun#
  expect("(")
  posfun# = pos(numeric_expr#)
  expect(")")
end function

' rpad$(s$, padded_len [, pad_string$])
function rpadfun$
  dim s as string, pad_string as string, padded_len as integer
  expect("(")
  s = strexpression$
  expect(",")
  padded_len = numeric_expr#
  pad_string = " "
  if accept&(",") then
    pad_string = strexpression$
  end if
  expect(")")

  rpadfun$ = s
  if len(s) > padded_len then
    rpadfun$ = mid$(s, 1, padded_len)
  else
    rpadfun$ = string$(padded_len - len(s), mid$(pad_string, 1, 1)) + s
  end if
end function

' replace$(haystack$, needle$ [, newst$])
function replacefun$
  dim haystack as string, needle as string, newst as string, start as integer, p as integer
  expect("(")
  haystack = strexpression$
  expect(",")
  needle = strexpression$

  newst = ""
  if accept&(",") then
    newst = strexpression$
  end if
  expect(")")

  start = 1
  do
    p = instr(start, haystack, needle)
    if p = 0 then exit do
    haystack = mid$(haystack, 1, p - 1) + newst + mid$(haystack, p + len(needle))
    start = p + len(newst) + 1
  loop

  replacefun$ = haystack
end function

' ubound(array-name)
function uboundfun&
  dim i as long
  expect("(")
  i = find_vname(sym)
  if i = 0 then
    print at_line$; "ubound: not an array: "; sym: errors = true
  else
    uboundfun& = var_names(i).hi_bnd
  end if
  call getsym
  expect(")")
end function

' screen(row, col)
function screenfun&
  dim row as long, col as long
  expect("(")
  row = numeric_expr#
  expect(",")
  col = numeric_expr#
  expect(")")
  screenfun& = screen(row, col)
end function

'------------------------------------------------------------------------
' expression parser
'------------------------------------------------------------------------

function binary_prec&(op as string)
  select case op
    case "^":                              binary_prec& = 14
    case "*", "/":                         binary_prec& = 12
    case "\" :                             binary_prec& = 11
    case "mod":                            binary_prec& = 10
    case "+", "-":                         binary_prec& = 9
    case ">>", "<<", "shl", "shr":         binary_prec& = 8
    case "=", "<>", "<", ">", "<=", ">=":  binary_prec& = 7
    case "and":                            binary_prec& = 5
    case "or":                             binary_prec& = 4
    case "xor":                            binary_prec& = 3
    case "eqv":                            binary_prec& = 2
    case "imp":                            binary_prec& = 1
    case else:                             binary_prec& = 0
  end select
end function

function get_paren_numeric#
  call getsym
  expect("(")
  get_paren_numeric# = numeric_expr#
  expect(")")
end function

function get_paren_string$
  call getsym
  expect("(")
  get_paren_string$ = strexpression$
  expect(")")
end function

function strfactor$
  dim x as integer
  dim s as string

  select case sym
    case "chr$":       strfactor$ = chr$(get_paren_numeric#)
    case "command$":   call getsym: strfactor$ = command$
    case "date$":      call getsym: strfactor$ = date$
    case "environ$":   strfactor$ = environ$(get_paren_string$)
    case "hex$":       strfactor$ = hex$(get_paren_numeric#)
    case "inkey$":     call getsym: strfactor$ = inkey$
    case "input$":     strfactor$ = input$(get_paren_numeric#)
    case "lcase$":     strfactor$ = lcase$(get_paren_string$)
    case "left$"
      call getsym:
      expect("(")
      s = strexpression$
      expect(",")
      x = numeric_expr#
      strfactor$ = left$(s, x)
      expect(")")
    case "lpad$":      call getsym: strfactor$ = lpadfun$
    case "ltrim$":     strfactor$ = ltrim$(get_paren_string$)
    case "mid$":       call getsym: strfactor$ = midfun$
    case "mki$":       strfactor$ = mki$(get_paren_numeric#)
    case "oct$":       strfactor$ = oct$(get_paren_numeric#)
    case "replace$":   call getsym: strfactor$ = replacefun$
    case "right$"
      call getsym
      expect("(")
      s = strexpression$
      expect(",")
      x = numeric_expr#
      strfactor$ = right$(s, x)
      expect(")")
    case "rpad$":      call getsym: strfactor$ = rpadfun$
    case "rtrim$":     strfactor$ = rtrim$(get_paren_string$)
    case "space$":     strfactor$ = space$(get_paren_numeric#)
    case "str$":       strfactor$ = str$(get_paren_numeric#)
    case "string$"
      call getsym ' string$(n [, strexpr])
      expect("(")
      x = numeric_expr#
      expect(",")
      if symtype = tystring or symtype = tystrident then
        strfactor$ = string$(x, strexpression$)
      else
        strfactor$ = string$(x, numeric_expr#)
      end if
      expect(")")
    case "time$":      call getsym: strfactor$ = time$
    case "trim$":      strfactor$ = ltrim$(rtrim$(get_paren_string$))
    case "ucase$":     strfactor$ = ucase$(get_paren_string$)

    case else
      if symtype = tystring then
        strfactor$ = mid$(sym, 2, len(sym) - 1)
        call getsym
      elseif symtype = tystrident then
        if peek_ch$ = "(" then
          strfactor$ = get_string_array_value$
        else
          strfactor$ = string_store(getstrindex&(right_side))
        end if
      else
        print at_line$; "In strfactor, expecting an operand, found: "; sym; " symtype is: "; symtype: errors = true
        call getsym
      end if
  end select
end function

function frac#(n as double)
    frac# = n - fix(n)
end function

function primary#
  dim i as double

  select case sym
    case "-":     call getsym: primary# =    -numeric_expr2#(unaryminus_prec)
    case "+":     call getsym: primary# =     numeric_expr2#(unaryplus_prec)
    case "not":   call getsym: primary# = not numeric_expr2#(unarynot_prec)

    case "abs":   primary# = abs(get_paren_numeric#)
    case "acos":  primary# = halfpi - asin2(get_paren_numeric#)
    case "acosh": primary# = acosh(get_paren_numeric#)
    case "acot":  primary# = halfpi - atn(get_paren_numeric#)
    case "acoth": primary# = acoth(get_paren_numeric#)
    case "acsc":  primary# = asin2(1 / get_paren_numeric#)
    case "acsch": primary# = acsch(get_paren_numeric#)

    case "asc":   primary# = asc(get_paren_string$)

    case "asec":  primary# = halfpi - asin2(1 / get_paren_numeric#)
    case "asech": primary# = asech(get_paren_numeric#)
    case "asin":  primary# = asin2(get_paren_numeric#)
    case "asinh": primary# = asinh(get_paren_numeric#)
    case "atanh": primary# = atanh(get_paren_numeric#)
    case "atn", "atan": primary# = atn(get_paren_numeric#)
    case "cdbl":  primary# = cdbl(get_paren_numeric#)
    case "cint":  primary# = cint(get_paren_numeric#)
    case "clng":  primary# = clng(get_paren_numeric#)
    case "cos":   primary# = cos(get_paren_numeric#)
    case "cosh":  primary# = cosh(get_paren_numeric#)
    case "cot":   primary# = 1 / tan(get_paren_numeric#)
    case "coth":  primary# = 1 / tanh(get_paren_numeric#)
    case "csc":   primary# = 1 / sin(get_paren_numeric#)
    case "csch":  primary# = 1 / sinh(get_paren_numeric#)
    case "csng":  primary# = csng(get_paren_numeric#)

    case "csrlin":call getsym: primary# = csrlin
    case "cvd":   primary# = cvd(get_paren_string$)
    case "cvi":   primary# = cvi(get_paren_string$)
    case "eof":   call getsym: primary# = eoff

    case "exp":   primary# = exp(get_paren_numeric#)

    case "false": call getsym: primary# = false

    case "frac":  primary# = frac#(get_paren_numeric#)
    case "fix":   primary# = fix(get_paren_numeric#)

    case "instr": call getsym: primary# = instrfun&

    case "int":   primary# = int(get_paren_numeric#)

    case "len":   primary# = len(get_paren_string$)

    case "ln":    primary# = log(get_paren_numeric#)
    case "log"
      call getsym:
      expect("(")
      i = log(numeric_expr#)
      if accept&(",") then
        primary# = i / log(numeric_expr#)
      else
        primary# = i
      end if
      expect(")")

    case "log10": primary# = log(get_paren_numeric#) / log(10)

    case "peek":  primary# = peekfun#(get_paren_string$)
    case "point": call getsym: primary# = pointfun#
    case "pos":   call getsym: primary# = posfun#
    case "rnd"
      call getsym
      if accept&("(") then
        primary# = rnd(numeric_expr#)
        expect(")")
      else
        primary# = rnd
      end if
    case "screen":call getsym: primary# = screenfun&

    case "sec":   primary# = 1 / cos(get_paren_numeric#)
    case "sech":  primary# = 1 / cosh(get_paren_numeric#)
    case "sgn":   primary# = sgn(get_paren_numeric#)
    case "sin":   primary# = sin(get_paren_numeric#)
    case "sinh":  primary# = sinh(get_paren_numeric#)
    case "sqr", "sqrt": primary# = sqr(get_paren_numeric#)
    case "tan":   primary# = tan(get_paren_numeric#)
    case "tanh":  primary# = tanh(get_paren_numeric#)

    case "timer": call getsym: primary# = timer
    case "true":  call getsym: primary# = true
    case "ubound": call getsym: primary# = uboundfun
    case "val":   primary# = val(get_paren_string$)

    case "irnd": primary# = int(rnd * int(get_paren_numeric#)) + 1
    case "@": primary# = atarray(get_paren_numeric#)

    case else
      if left$(sym, 1) = "_" then
        print "Unknown function: "; sym: errors = true: call getsym
      elseif symtype = tynum then
        primary# = the_num
        call getsym
      elseif symtype = tyident then
        if peek_ch$ = "(" then
          primary# = get_numeric_array_value#
        else
          primary# = numeric_store(getvarindex&(right_side))
        end if
      else
        print at_line$; "In primary, expecting an operand, found: "; sym; " symtype is: "; symtype: errors = true
        call getsym
      end if
  end select
end function

function strexpression$
  dim s as string
  s = strfactor$
  while accept&("+")
    s = s + strfactor$
  wend
  strexpression$ = s
end function

'-------------------------------------------------------------------------------------------------

sub push_str(s as string)
  str_st_ndx = str_st_ndx + 1
  str_stack(str_st_ndx) = s
end sub

sub push_num(n as double)
  num_st_ndx = num_st_ndx + 1
  num_stack(num_st_ndx) = n
end sub

function pop_str$
  pop_str = str_stack(str_st_ndx)
  str_st_ndx = str_st_ndx - 1
end function

function pop_num#
  pop_num = num_stack(num_st_ndx)
  num_st_ndx = num_st_ndx - 1
end function

function evalstrexpr&(op as string)
  dim s as string, s2 as string, n as double

  s2 = pop_str$
  s = pop_str$
  select case op
    case "=":   n = s = s2
    case "<>":  n = s <> s2
    case "<":   n = s <  s2
    case ">":   n = s >  s2
    case "<=":  n = s <= s2
    case ">=":  n = s >= s2
    case else
      print at_line$; "In expr, expecting a string operator, found: "; op; " symtype is: "; symtype: errors = true
      call getsym
  end select
  push_num(n)
  evalstrexpr& = tynum
end function

function evalnumericexpr&(op as string)
  dim n as double, n2 as double

  n2 = pop_num#
  n = pop_num#
  select case op
    case "^":   n = n ^   n2
    case "*":   n = n *   n2
    case "/":   if n2 = 0 then print at_line$; "division by 0": errors = true else n = n /   n2
    case "\":   if n2 = 0 then print at_line$; "division by 0": errors = true else n = n \   n2
    case "mod": if n2 = 0 then print at_line$; "division by 0": errors = true else n = n mod n2
    case "+":   n = n +   n2
    case "-":   n = n -   n2
    case "=":   n = n =   n2
    case "<>":  n = n <>  n2
    case "<":   n = n <   n2
    case ">":   n = n >   n2
    case "<=":  n = n <=  n2
    case ">=":  n = n >=  n2
    case "and": n = n and n2
    case "or":  n = n or  n2
    case "xor": n = n xor n2
    case "eqv": n = n eqv n2
    case "imp": n = n imp n2
    case "shl","<<": n = shlf#(n, n2)
    case "shr",">>": n = shrf#(n, n2)
    case else
      print at_line$; "In expr, expecting a numeric operator, found: "; op; " symtype is: "; symtype: errors = true
      call getsym
  end select
  push_num(n)
  evalnumericexpr& = tynum
end function

' return the type of expression, either string or numeric; result is on the stack
function any_expr&(p as integer)
  dim left_type as integer

  ' we need to decide which primary to call - numeric or string
  ' leading parens don't tell us which primary, so just do recursive call
  if accept&("(") then
    left_type = any_expr&(0)
    expect(")")
  elseif symtype = tystring or symtype = tystrident then
    push_str(strexpression$)
    left_type = tystring
  elseif symtype = tynum or symtype = tyident or sym = "-" or sym = "+" or sym = "not" then
    push_num(primary#)
    left_type = tynum
  elseif sym = "@" then
    push_num(primary#)
    left_type = tynum
  elseif sym = "" then
    print at_line$; "In expr, unexpected end-of-line found: "; pgm(curline): errors = true
  else
    print at_line$; "In expr, expecting an expr, found: "; sym; " symtype is: "; symtype; " - near column: "; textp
    errors = true
    call getsym
  end if

  do      ' while binary operator and precedence(sym) >= p
    dim op as string
    dim right_type as integer, prec as integer

    prec = binary_prec&(sym)
    if prec = 0 or prec < p then exit do

    op = sym

    call getsym

    ' all operators are left associative in qbasic
    prec = prec + 1

    right_type = any_expr&(prec)

    if left_type = tystring and right_type = tystring then
      left_type = evalstrexpr&(op)
    elseif left_type = tynum and right_type = tynum then
      left_type = evalnumericexpr&(op)
    else
      print at_line$; "type missmatch in expr - left_type:"; left_type; " right_type:"; right_type: errors = true
      call getsym
    end if
  loop
  any_expr& = left_type
end function

function numeric_expr2#(p as integer)
  if any_expr&(p) = tynum then
    numeric_expr2# = pop_num#
  else
    print at_line$; "numeric expression expected": errors = true
  end if
end function

' process and return a numeric expression
function numeric_expr#
  numeric_expr# = numeric_expr2#(0)
end function

function bool_expr&
  bool_expr& = (numeric_expr# <> 0)
end function

'------------------------------------------------------------------------
'  scanner
'------------------------------------------------------------------------
sub init_scanner
  dim i as integer

  for i = 0 to 255
    ctype_arr(i) = ct_unknown
  next

  ' alpha
  for i = asc("a") to asc("z")
    ctype_arr(i) = ct_alpha
  next
  for i = asc("A") to asc("Z")
    ctype_arr(i) = ct_alpha
  next
  ctype_arr(asc("_")) = ct_alpha

  ' num
  for i = asc("0") to asc("9")
    ctype_arr(i) = ct_digit
  next

  ctype_arr(asc(".")) = ct_period
  ctype_arr(asc(",")) = ct_punc1
  ctype_arr(asc(";")) = ct_punc1
  ctype_arr(asc("=")) = ct_punc1
  ctype_arr(asc("+")) = ct_punc1
  ctype_arr(asc("-")) = ct_punc1
  ctype_arr(asc("*")) = ct_punc1
  ctype_arr(asc("/")) = ct_punc1
  ctype_arr(asc("\")) = ct_punc1
  ctype_arr(asc("^")) = ct_punc1
  ctype_arr(asc("(")) = ct_punc1
  ctype_arr(asc(")")) = ct_punc1
  ctype_arr(asc("?")) = ct_punc1
  ctype_arr(asc(":")) = ct_punc1
  ctype_arr(asc("#")) = ct_punc1
  ctype_arr(asc("@")) = ct_punc1
  ctype_arr(asc("$")) = ct_dollar
  ctype_arr(asc("<")) = ct_lt
  ctype_arr(asc(">")) = ct_gt
  ctype_arr(asc("&")) = ct_amp
  ctype_arr(asc(chr$(34))) = ct_dquote
  ctype_arr(asc(chr$(39))) = ct_squote
end sub

function peek_ch$
  peek_ch$ = left$(ltrim$(the_ch) + ltrim$(mid$(pgm(curline), textp)), 1)
end function

' other code relies on textp always being incremented; so do it even on EOL
sub getch
  the_ch = ""
  if textp <= len(thelin) then
    the_ch = mid$(thelin, textp, 1)
  end if
  textp = textp + 1
'print "getch: textp: "; textp; " the_ch: "; the_ch; " thelin: "; thelin
end sub

sub readident
  sym = ""
  do while the_ch <> ""
    if ctype_arr(asc(the_ch)) <> ct_alpha and ctype_arr(asc(the_ch)) <> ct_digit then exit do
    sym = sym + lcase$(the_ch)
    getch
  loop

  symtype = tyident

  select case the_ch
    case "%", "&", "!", "#":        sym = sym + the_ch: getch ' just ignore
    case "$": symtype = tystrident: sym = sym + the_ch: getch ' string
      ' see if we have "end if", if so, convert to "endif"
    case " "
      if sym = "end" then
        if lcase$(mid$(thelin, textp, 2)) = "if" then
          sym = "endif"
          getch ' skip " "
          getch ' skip "i"
          getch ' skip "f"
        end if
      end if
  end select
end sub

sub readnumber
  sym = ""
  do while the_ch <> ""
    if ctype_arr(asc(the_ch)) <> ct_digit then exit do
    sym = sym + the_ch
    getch
  loop
  if the_ch = "." then
    sym = sym + the_ch
    getch
    do while the_ch <> ""
      if ctype_arr(asc(the_ch)) <> ct_digit then exit do
      sym = sym + the_ch
      getch
    loop
  end if
  if lcase$(the_ch) = "e" then
    sym = sym + "e"
    getch
    if the_ch = "+" or the_ch = "-" then sym = sym + the_ch: getch
    do while the_ch <> ""
      if ctype_arr(asc(the_ch)) <> ct_digit then exit do
      sym = sym + the_ch
      getch
    loop
  end if
  the_num = val(sym)
  symtype = tynum
end sub

' on entry pointing to 'h'
sub readhex
  sym = "&h"
  getch     ' skip the 'h'
  do while the_ch <> ""
    if ctype_arr(asc(the_ch)) <> ct_digit and instr("abcdefABCDEF", the_ch) = 0 then exit do
    sym = sym + the_ch
    getch
  loop
  the_num = val(sym)
  symtype = tynum
end sub

sub readstr
  sym = chr$(34)
  getch
  while the_ch <> chr$(34)
    if the_ch = "" then
      print at_line$; "string not terminated": errors = true
      exit sub
    end if
    sym = sym + the_ch
    getch
  wend
  getch
  symtype = tystring
end sub

sub skiptoeol
  textp = len(thelin) + 1
  the_ch = ""
  sym = ""
  symtype = tyunknown
end sub

function gettoeol$
  dim s as string
  s = ""
  while the_ch <> ""
    s = s + the_ch
    getch
  wend
  call getsym
  gettoeol$ = s
end function

' symtype: unknown, tystring, tynum, tyident, tystrident
' sym: the symbol just read, above, and punctuation
sub getsym
'print "in getsym"
  'dim ttt as double
  'ttt = timer
  'nsyms = nsyms + 1
  sym = ""
  symtype = tyunknown
  ' skip white space
  while the_ch <= " "
    if the_ch = "" then exit sub else getch
  wend
  sym = the_ch
  select case ctype_arr(asc(the_ch))
    case ct_punc1:            getch       'punctuation
    case ct_alpha:            readident   'identifier
    case ct_digit, ct_period: readnumber  'number
    case ct_dquote:           readstr     'double quote
    case ct_squote:           skiptoeol   'comment
    case ct_lt
      getch
      if instr("=><", the_ch) > 0 then sym = sym + the_ch: getch '<=, <> <<
    case ct_gt
      getch
      if the_ch = "=" or the_ch = ">" then sym = sym + the_ch: getch ' >=, >>
    case ct_amp:
      getch
      if the_ch = "H" or the_ch = "h" then
        readhex
      else
        print at_line$; "getsym: '& found, expecting 'h' but found:"; the_ch: errors = true
      end if
    case ct_dollar:
      if textp = 2 then skiptoeol else goto boguschar
    case else
      boguschar:
      print at_line$; "getsym: unexpected character read:"; the_ch: errors = true
      getch
  end select
  'scantime = scantime + (timer - ttt)
end sub

sub initgetsym(n as long, col as integer)
'print "initgetsym"
  curline = n
  textp = col
  thelin = pgm(curline)
  the_ch = " "
  call getsym
end sub

function fileexists%(filename as string)
    dim f, existing as long

    f = freefile
    open filename for append as #f
    existing = lof(f) > 0
    close #f
    if not existing then kill filename  ' delete empty files
    fileexists = existing
end function
