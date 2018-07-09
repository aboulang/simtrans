;;; -*- Package: CGOL -*-

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;  S I M U L A   P A C K A G E   ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;+++ This really should work in another package, but there is trouble in redefining
;;;+++ one char operators such as "." since the tokenizer always returns them in the
;;;+++ cgol package.

;;;+++ MIGHT WANT TO PARSE ARG DECS AND PUT INTO DOCUMENTATION FOR FUNCTION

;;;"SIMULA"		%Base language%
;;;"SIMMAINBODY"	%Language for procedures, functions and classes in the main body%$
;;;"SIMCLASSPROC"	%language for procedures and begin blocks in a class%$
;;;"SIMCLASSPROCBODY"	%language for type declarations in begin blocks in class procedure%$
;;;"SIMPROCBODY"	%language for type declarations in begin blocks in a procedure%$
;;;"SIMARRDEC"		%language for array declarations%$

(eval-when (load eval compile)
  (loop for symbol in `(cgol:learn cgol:speak cgol:forget cgol:resetlanguage
				   cgol:token cgol:left cgol:right cgol:parselist
				   cgol:deprognify cgol:getvarlist cgol:pkgcheck cgol:advance)
	do (globalize symbol)))

(defsubst my-flavor (instance)
  (si:%instance-flavor instance))

(defsubst flavor (name)
  (get name 'si:flavor))


(defsubst flavor-get (flavor indicator)
  (get (locf (si:flavor-plist flavor)) indicator))
 
(defsubst flavor-put (flavor property indicator)
  (putprop (locf (si:flavor-plist flavor)) property indicator))


;;;BASE FLAVOR FOR SIMULA OBJECT 
(defflavor sim-object () ()
  (:special-instance-variables
   :settable-instance-variables))

(defvar TRUE T)
(defvar FALSE NIL)
(defvar NONE NIL)
(defvar NOTEXT "")

(defvar *CLASS*)

(defvar *default-array-type* ':art-float)

(defconst *array-type-alist* '((real :art-float)
			       (integer :art-32b)
			       (boolean :art-q)	;or art-1b?
			       (character :art-string)
			       (ref :art-q)
			       (text :art-q)))



;;;---------------- begin macro ----------------
;;;used to handle simula BEGIN .... END blocks
;;;simula turns something like:
;;;
;;;BEGIN
;;; INTEGER FOO,BAR;
;;; REAL ARRAY BAZ[1:20],BLITZ[0:30];
;;; I := 1;
;;; END;
;;;
;;; into
;;;
;;;(begin
;;;   (integer foo bar)
;;;   (real (defsimarray (baz 1 20) (blitz 0 30)))
;;;   (setq i 1))
;;;
;;; and begin turns into
;;;
;;;(prog ((foo nil)
;;;       (bar nil)
;;;       (baz (make-array '(20) ':type ':art-float ':leader-list '(1)))
;;;       (blitz (make-array '(30) ':type ':art-float ':leader-list '(0)))
;;;
;;;  ALSO
;;;integer foo,array bar[1:20]; at top level becomes
;;;
;;;(defsimvar (integer foo (defsimarray (baz 1 20))))
;;;
;;;which becomes
;;;(progn 'compile (defvar foo nil "type: integer")
;;;                (defvar bar (make-array '(20) ':type ':art-32b ':leader-list '(1))
;;;                            "type: integer"))
(comment
(begin
  ((ref zap) (defsimarray (sef 1 20 30 40)))
  (integer foo bar)
  (integer (defsimarray (baz 1 20) (blitz 0 30)))
  (setq i 1)))


(defmacro defsimvar (declaration &aux (type (first declaration)))
  (and (listp (car declaration)) (equal (caar declaration) 'ref)
       (setf (car declaration) 'ref))
  (loop with var-list = (cdr (process-declaration declaration))
	for var-form in var-list
	when (equal var-form (third var-list))
	append var-form into forms
	else append (loop for item in var-form
			  collect `(defvar ,@item ,(format nil "Type: ~A" type))) into forms
	finally (return `(progn 'compile ,@forms))))


(comment
(begin
  ((ref zap) (defsimarray (sef 1 20 30 40)))
  (integer foo bar)
  (integer (defsimarray (baz 1 20) (blitz 0 30)))
  (defsimproc bar  (args) (begin)( 'defun)
  (setq i 1))))

(defun defsimfun (type defining-form)
  (let* ((type-def (first defining-form))
	 (name-form (second defining-form))
	 (name (if (listp name-form) (intern-local (car (last name-form))) name-form))
	 (new-args `(,@(third defining-form) &aux ,name))	;locally bind fun name var
	 (new-body `(,(format nil "Type: ~A" type)		;documentation string
		     ,@(rest3 defining-form) ,name)))		;insure fun name var is return
    `(,type-def ,name-form ,new-args ,@new-body)))

(defun process-declaration (dec &aux functions arrays vars vars-for-class)
  (cond ((equal (first dec) 'defsimarray)
	 (setq arrays (append  arrays (macroexpand-1 dec)))
	 (setq vars-for-class			;ARRAYS GOES ON VARS-FOR-CLASS LIST TOO!
	       (append vars-for-class `((,(first (second dec)) nil)))))	
	((equal (first dec) 'defsimproc)
	 (setq functions (append (process-forms (macroexpand-1 dec)) functions)))
	((and (listp (second dec)) (equal (first (second dec)) 'defsimproc))
	 (setq functions (append (process-forms
				   (defsimfun (first dec) (macroexpand-1 (second dec))))
				 functions)))
	(t (loop with *default-array-type* = (second (assoc (first dec) *array-type-alist*))
		 for var in (cdr dec)
		 when (listp var)
		 append (macroexpand-1 var) into arrs and		;defsimarray forms
		 collect `(,(first (second var)) nil) into vrs-for-class
		 else collect `(,var nil) into vrs and
		 collect  `(,var nil) into vrs-for-class
		 finally (setq arrays (append arrays arrs)) 
		         (setq vars   (append vars vrs))
			 (setq vars-for-class (append vars-for-class vrs-for-class)))))
  `(,vars-for-class ,vars ,arrays ,functions))

(defun process-forms (functions)
  (if (and (equal (first functions) 'progn) (equal (second functions) ''compile))
      (rest2 functions)
      `(,functions)))

;;;For begins that have procedures in them [ones fro the bodies of procedures]
(defmacro begin-internal (&BODY VARS-AND-EXPS)
  (loop with new-forms
	for item in vars-and-exps
	when (symbolp item)
	collect (list item) into exps		;atoms are function calls
	else when (or (member (car item) `(boolean integer character
						   real text defsimproc defsimarray))
		      (and (listp (car item)) (equal (caar item) 'ref)
			   (setf (car item) 'ref))
		      (and (equal (car item) 'progn) (equal (second item) ''compile)))
             do (setq new-forms  (process-declaration item)) and
	     append (second new-forms) into vars and
	     append (first new-forms) into vars-for-class and
	     append (third new-forms) into arrays and
	     append `(,@(first new-forms)
		      ,@(third new-forms)) into vars-arrays and	  ;for prog
       	     append (fourth new-forms) into functions
     	     else when (equal (car item) '%%%go-label%%%)
	     ;;WHY WHY WHY????
	          ;;append `(,@(second item) ,@(rest2 item)) into exps
	          append (rest1 item) into exps
	          else collect item into exps
	finally (RETURN `((prog ,vars-arrays ,@exps)	;default prog form
			  ,vars ,vars-for-class ,arrays ,functions ,exps))))
				
(defmacro begin (&body vars-and-exps)
  (loop with new-forms
	for item in vars-and-exps
	when (symbolp item)
	collect (list item) into exps		;atoms are function calls
	else when (or (member (car item) `(boolean integer character
						   real text defsimproc defsimarray))
		      (and (listp (car item)) (equal (caar item) 'ref)
			   (setf (car item) 'ref))
		      (and (equal (car item) 'progn) (equal (second item) ''compile)))
            do (setq new-forms  (process-declaration item)) and
	    append `(,@(second new-forms)
		     ,@(third new-forms)) into vars-arrays and	  ;for prog
	    append (fourth new-forms) into functions 
	    else when (equal (car item) '%%%go-label%%%)
	         append (rest1 item) into exps
	         else collect item into exps
	finally (return `(prog ,vars-arrays ,@exps))))


(comment
(defsimproc bbbbb (more-args jkfkjf)
(begin-internal
  ((ref zap) (defsimarray (sef 1 20 30 40)))
  (integer foo bar)
  (integer (defsimarray (baz 1 20) (blitz 0 30)))
  (defsimproc bar  (fargs) (begin-internal
			     ((ref zap) (defsimarray (sef 1 20 30 40)))
			     (integer foo bar)
			     (integer (defsimarray (baz 1 20) (blitz 0 30)))
			     (defsimproc barr  (fargs) (begin-INTERNAL
							 (defsimarray (baz 1 20))
							 (integer foo bar)
							 (setq i 1))) 
			     (setq i 1)))
  (setq i 1))
defmethod foo))



(defmacro defsimproc (name args body &optional (type  'defun) class)
  (let*
    ((ex-body        (macroexpand-1 body))	;assumes begin-internal block
     (nbody          (first ex-body))		;prog form
     (vars           (second ex-body))		;local vars
     (vars-for-class (third ex-body))		;var for class defs
     (arrays         (fourth ex-body))		;arrays (not really needed)
     (functions	     (fifth ex-body))		;functions to be brought outside
     (exps           (sixth ex-body)))		;expressions in body
    (if functions
	`(progn 'compile
		;;MAKE DEFINITION
		,(make-definition name args nbody type class) 
		;;DEFINE THE INNER FUNCTIONS/METHODS
		,@functions)
	(make-definition name args nbody type class))))


(defun make-definition (name args exbody type class)
  `(,@(selectq  type
	(defmethod    `(defmethod (,class ,(intern-local name 'user))))
	(defun-method `(defun-method ,name ,class))
	(defun        `(defun ,name)))
    ,args
    ,exbody))

;;;+++ skip the flavor-put if it has no initable instance vars
(defmacro defsimclass (name initable-instance-vars body &optional (mixin 'sim-object))
  (let*
    ((ex-body        (macroexpand-1 body))	;assumes begin-internal block
     (nbody          (first ex-body))		;prog form
     (vars           (second ex-body))		;local vars
     (vars-for-class (third ex-body))		;var for class defs
     (init-arrays    (fourth ex-body))		;arrays 
     (methods	     (fifth ex-body))		;functions to be brought outside
     (init-body      (sixth ex-body)))		;expressions in body
    `(progn 'compile
	    ;;MAKE THE FLAVOR
	    (defflavor ,name (,@initable-instance-vars ,@vars-for-class)
		       (,mixin)
	      (:initable-instance-variables ,@initable-instance-vars))
	    ;;PUT UP INIT IV INFO (COULD USE SI:FLAVOR-INITABLE-INSTANCE-VARIABLES)
	    (FLAVOR-PUT (FLAVOR ',NAME) ',initable-instance-vars 'INIT-VARS)
	    ;;DEFINE THE METHODS
	    ,@methods
	    ;;BUILD UP INIT METHOD
	    (defmethod (,name :init) (plist)
	      ,@(loop for init-array in init-arrays
		      collect `(setf ,@init-array))
	      ,@init-body))))

;;;================================================================;;;
;;;			 array stuff & misc			   ;;;
;;;================================================================;;;

(defmacro new (flavor-name &rest args &aux flavor)
  (or (setq flavor (flavor flavor-name))
      (format t "~&Warning: Flavor ~A not defined yet." flavor-name))
  (if flavor
    (let* ((init-vars (flavor-get flavor 'init-vars))
	   (init-list (loop for arg in args
			    for init-var in init-vars
			    collect `',(intern-local init-var 'user)
			    collect arg)))
      `(make-instance ,flavor-name ,@init-list))
    `(lexpr-funcall #'make-instance ,flavor-name (build-init-list ,flavor-name ,@args))))

(defmacro my-inspect (instance form)
  ;;assumes all vars to be special so I can access in instance
  ;;(I need the calee contour!)
  `(send ,instance ':eval-inside-yourself ,form))


;;;For (sim-send foo (baz 1 2)) and
;;;    (sim-send foo baz)
(defmacro sim-send (sim-object message)
  `(send ,sim-object ,@(if (listp message)
			   `(',(intern-local (car message) 'user) ,@(cdr message))
			   `(',(intern-local message 'user)))))

;;;left QUA  right.f either a reference to left or (send left ':f)
(defmacro qua (left right)
  (if (listp right)
      `(sim-send ,left ,(third right))
      left))

;;;+++ THIS needs an array data base sometime. This will mean that the BEGIN-INTERNAL
;;;+++ form needs to expand all (defsimarray ...) forms etc. Also would be worthwile
;;;+++ to have the BEGIN-INTERNAL form turn into a BEGIN form.
(comment
(DEFSIMARRAY (:PKTRATE 1 :MAXLINES 0 1)))

(defmacro defsimarray (&rest arrays)
  (loop for array in arrays
	collect `( ,(first array) ,(make-array-form (cdr array)))))


(defun make-array-form (dims)
  (loop for (low high) on dims by 'cddr
	;;FOR NOW ASSUME LOW = 1
	when (and (numberp low)
		  (> 0 low))
	do (format t "Low index ~A less than 0: You will LOOSE!~%" low)
	when (and (numberp low)
		  (< 2 low))
	do (format t "Low index ~A > 2: You might want to check that.~%" low)
	;;collect `(1+ (- ,high ,low)) into sizes 
	collect   `(1+ ,high) into sizes
	collect `(- ,low) into offsets
	finally (return `(make-array (list ,@sizes)
				     ':type ',*default-array-type*
				     ':leader-list (list ,@offsets)))))

;;; ASSUMES ARRAY ALREADY DEFINED
;;;(simula-aref baz 2)
;;;(simula-aset 10 baz 2)
;;;(setf (simula-aref baz 2) 10)
(defmacro simula-aref (array &rest subscripts)	
  (let ((new-subscripts (loop for subscript in subscripts
			     for i from 0 to (- (length subscripts) 1)
			     ;;FOR NOW SINCE THIS DOESN'T WORK SINCE IT ASSUMES ARRAY IS MADE!
			     ;;collect (+ subscript (array-leader (eval array) i)))))
			     collect subscript)))
    `(aref ,array ,@new-subscripts)))



(defmacro simula-aset (value array &rest subscripts)
  (let ((new-subscripts (loop for subscript in subscripts
			     for i from 0 to (- (length subscripts) 1)
			     ;;FOR NOW SINCE THIS DOESN'T WORK SINCE IT ASSUMES ARRAY IS MADE!
			     ;;collect (+ subscript (array-leader (eval array) i)))))
			     collect subscript)))	
    `(aset ,value ,array ,@new-subscripts)))


(defprop simula-aref simula-aref-setf :setf)

(defun simula-aref-setf (ref val)
   `(simula-aset ,val ,(second ref) . ,(rest2 ref)))

;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; CGOL HERE ON DOWN! ;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;+++ TO DO:
;;;+++  IS, IN, QUA, full INSPECT, ACTIVATE, INNER
;;;+++  prefix BEGIN 
;;;+++  A parselist until token (don't absorb the token).
;;;+++   This will enable to parse full simula procedures and the BEGIN stmt;... stmt; END
;;;+++   problem.
;;;+++ It would be nice to have cgol strings be real strings instead of || sequences.

;;;I have to redefine this when another package is used for other languages.
;;;There is one problem left: Single token operators are always in the cgol package!
(comment
cgol:(progn #.(cgol)
prefix "ITER" 2 
	new ivars, whenvar, result, body;
	while assoc(pkgcheck(token), !'(
(for    #$     ivars := (token .
		          if pkgcheck(advance) = ":=" then (advance; right exists) .
		          if pkgcheck(token) = "STEP" then
			 [if pkgcheck(advance) = "DITTO" then (advance; it) else right])
	                       . ivars$)
(when   #$     whenvar := right$)
(until  #$     whenvar := right$)
(while  #$     whenvar := ["NOT", right]$)
(return #$     result  := right$)
(do     #$     body    := right$)))
	       exists do (advance; eval cadr it);
	if not( ivars or whenvar or result or body) then body := right;
        ["DO", nreverse ivars, [whenvar, result]] @
           if not atom body and car body eq "PROGN"
              then cdr body else ncons body  $
	      
=exit$))
;;; These are for having tokens in more than one package work right
#.(cgol)
=resetlanguage$
!
(defun newcheck (x y &aux new-y)
  (when (symbolp x)
    (if (symbolp y) (setq new-y (list y)) (setq new-y y))
    (if (intern-soft x cgol:cgol-package)
	(member (intern-soft x cgol:cgol-package)
		(loop for del in new-y
		      collect (intern-soft del cgol:cgol-package)))
	(member x new-y)))) $
!
(defun cgol:check (del)
    (if (newcheck token del) (cgol:advance)
	(cgol:cgolerr (cgol:cat "MISSING " del " INSERTED BEFORE " token) 0 nil)))$
!
(defun cgol:parselist (rb delims)
  (cons (cgol:parse rb) (when (newcheck token delims)
			  (cgol:advance)
			  (cgol:parselist rb delims))))$


=learn "SIMULA"$

newtok  "\="$
newtok  "=/="$
newtok  "=="$

newtok  !|////|$

infix   !|////|	    10   ["FIX", is "QUOTIENT"] %integer division% $
prefix  "\"         10   is "NOT"$
infix   "^"         22   is arith("EXPT") $
infix	"LE"	    10	 ["NOT", is ARITH("GREATERP")]$
infix   "GE"	    10	 ["NOT", is ARITH("LESSP")] %use <=%$
infix	"LT"        10	 is arith("LESSP")$
infix   "GT"        10	 is arith("GREATERP")$

infix   "\="        10   ["NOT", is arith("EQUAL")]$
infix   "=/="       10   ["NOT", is "EQUAL"]$
infix   "=="        10   is "EQ"$
prefix  "THIS"      5    right;"SELF"$
prefix  "COMMENT"   5    is "COMMENT"$
infix   !|:|        10   !'|%%%GO-LABEL%%%| . LEFT . [RIGHT]		%for goto%$
prefix  "GOTO"	    5	 ["GO" , (TOKEN & ADVANCE)]$


prefix	"ARRAY"	10
speak "SIMARRDEC";
is "DEFSIMARRAY" &
forget$


infixd	"["	25 0    "SIMULA-AREF" . LEFT . PARSELIST(0,!'|,|) & check "]"$

infixd  ":="    25 1    is "SETF"$

newtok  ":-"$
infixd  ":-"    25 1    is "SETF" %simula denotes% $


infixr  !|.|    27      is "SIM-SEND" %not just send because of (send foo (baz args..))%$
infix   "QUA"   25      is "QUA"$

delim   "END"$

prefix  "NEW"      0
"NEW" . (TOKEN & ADVANCE)  .
        if newcheck(token,!'|(|)
           then (advance; PARSELIST(0,!'|,|) & check !'|)|)$


prefix	"INSPECT"   2	 "MY-INSPECT" .  right . [(check "DO" ; right)] $

prefix  "BOOLEAN"   5 	 ["DEFSIMVAR" , "BOOLEAN" . parselist(10,!'|,|)] $
prefix  "INTEGER"   5 	 ["DEFSIMVAR" , "INTEGER" . parselist(10,!'|,|)] $
prefix  "REAL"      5	 ["DEFSIMVAR" , "REAL"    . parselist(10,!'|,|)] $
prefix  "REF"       5	 ["DEFSIMVAR" ,("REF" . if newcheck(token,!'|(|)
	                                  then (advance; getvarlist & check !'|)|)) .
			                  parselist(10,!'|,|)]$
prefix  "CHARACTER" 5 	 ["DEFSIMVAR" , "CHARACTER" . parselist(10,!'|,|)] $
prefix  "TEXT"      5	 ["DEFSIMVAR" , "TEXT" . parselist(10,!'|,|)] $

prefix  "BEGIN"    0	
speak "SIMMAINBODY" ; % need to macro expand sometime%
(let exps = deprognify(right);
!`(progn ,@(loop for exp in exps
		 append (process-forms (macroexpand-1 exp))))) & CHECK "END" &
forget$

prefix	"FOR"	1 
new pars, argts, inon, fcn, body;
pars:= [token]; inon := advance; advance;
fcn := assoc(inon, !'((in (do mapc) (collect mapcar) (coalesce mapcan))
 		      (on (do map) (collect maplist) (coalesce mapcon))
	              (|:=| (do mapc))));
if fcn then fcn := cdr fcn 
  else cgolerr(inon cat " FOUND WHERE IN OR ON OR := EXPECTED", 2,t);
argts := [right];
while pkgcheck(token) eq !'|,| do
   (pars := advance . pars; advance; check inon; argts := right . argts);
fcn := assoc(pkgcheck(token), fcn); if fcn then fcn := cadr fcn
      else cgolerr(token cat " FOUND WHERE DO, COLLECT OR COALESCE EXPECTED",2,t);
advance; argts := nreverse argts; pars := nreverse pars; body := right;
if fcn = "MAPC" and and{(\x;not atom x and car x = "TO")[argts]}
	then "DO" .
	     (for p in pars, a in argts collect
 	       [p, cadr a, if cadddr a = 1 then ["ADD1", p]
					   else ["PLUS", p, cadddr a]]) .
	     [ORify((\p,a; ["GREATERP", p, caddr a])[pars,argts])] .
	     deprognify(body)
else fcn . ["FUNCTION", if cdr body = pars and atom car body then car body
			else ["LAMBDA", pars, body]] . argts $

infix "STEP" 18 "TO" . (left & right exists) . 
                         (check("UNTIL");right).
                         [it] $

%================ Sub Language Section ================%$

%================================================================%$
=learn "SIMMAINBODY" %Language for procedures, functions and classes in the main body%$

prefix  "BEGIN"    0
"BEGIN" . (if newcheck(token,"END") then nil else DEPROGNIFY(RIGHT)) & CHECK "END"
% (check !'|;|;check "END")%
%work on deprognify% $


prefix  "PROCEDURE" 0
speak "SIMPROCBODY";
"DEFSIMPROC" . (TOKEN & ADVANCE)  .
              (if newcheck(token,!'|(|)
                then (advance; PARSELIST(0,!'|,|) & check !'|)|) & check !'|;| ) .
              (check "BEGIN";
		     "BEGIN-INTERNAL" .
		     (if newcheck(token,"END") then nil else DEPROGNIFY(RIGHT))
		     & check "END") .
              ["DEFUN"] &
forget$

prefix   "CLASS"     0
speak "SIMCLASSPROC" ; ?*CLASS?* := TOKEN;
"DEFSIMCLASS" . (TOKEN & ADVANCE)  . 
                (if newcheck(token,!'|(|)
	           then (advance; PARSELIST(0,!'|,|) & check !'|)|) & check !'|;| ) .
               [(check "BEGIN";
		       "BEGIN-INTERNAL" .
		       (if newcheck(token,"END") then nil else DEPROGNIFY(RIGHT))
		       & check "END")] &
forget$

infixd  "CLASS"   25  0 
speak "SIMCLASSPROC" ; ?*CLASS?* := TOKEN;
"DEFSIMCLASS" . (TOKEN & ADVANCE)  . 
                (if newcheck(token,!'|(|)
	           then (advance; PARSELIST(0,!'|,|) & check !'|)|) & check !'|;| ) .
               (check "BEGIN";
		      "BEGIN-INTERNAL" .
		      (if newcheck(token,"END") then nil else DEPROGNIFY(RIGHT))
		      & check "END") .
               [left]  &
forget$



%================================================================%$
=learn  "SIMPROCBODY" %language for type declarations in begin blocks in a procedure%$

prefix  "BOOLEAN"   5 	 "BOOLEAN" . parselist(10,!'|,|) $
prefix  "INTEGER"   5 	 "INTEGER" . parselist(10,!'|,|) $
prefix  "REAL"      5	 "REAL"    . parselist(10,!'|,|) $
prefix  "REF"       5	 ("REF" . if newcheck(token,!'|(|)
	                           then (advance; getvarlist & check !'|)|)) .
			           parselist(10,!'|,|)$
prefix  "CHARACTER" 5 	 "CHARACTER" . parselist(10,!'|,|) $
prefix  "TEXT"      5	 "TEXT" . parselist(10,!'|,|) $

prefix  "PROCEDURE" 0
"DEFSIMPROC" . (TOKEN & ADVANCE)  .
              (if newcheck(token,!'|(|)
                then (advance; PARSELIST(0,!'|,|) & check !'|)|) & check !'|;| ) .
             (check "BEGIN";
		    "BEGIN-INTERNAL" .
		    (if newcheck(token,"END") then nil else DEPROGNIFY(RIGHT))
		    & check "END") .
             ["DEFUN"]$

%================================================================%$
=learn "SIMCLASSPROC" %language for procedures and begin blocks in a class%$

prefix  "BOOLEAN"   5 	 "BOOLEAN" . parselist(10,!'|,|) $
prefix  "INTEGER"   5 	 "INTEGER" . parselist(10,!'|,|) $
prefix  "REAL"      5	 "REAL"    . parselist(10,!'|,|) $
prefix  "REF"       5	 ("REF" . if newcheck(token,!'|(|)
	                           then (advance; getvarlist & check !'|)|)) .
			           parselist(10,!'|,|)$
prefix  "CHARACTER" 5 	 "CHARACTER" . parselist(10,!'|,|) $
prefix  "TEXT"      5	 "TEXT" . parselist(10,!'|,|) $


prefix  "PROCEDURE" 0  
speak "SIMCLASSPROCBODY" ;
"DEFSIMPROC" . (TOKEN & ADVANCE) .
              (if newcheck(token,!'|(|)
                 then (advance; PARSELIST(0,!'|,|) & check !'|)|) & check !'|;| ) .
	       (check "BEGIN";
		      "BEGIN-INTERNAL" .
		      (if newcheck(token,"END") then nil else DEPROGNIFY(RIGHT))
		      & check "END") .
               "DEFMETHOD" .
               [?*CLASS?*] &
forget$

%================================================================%$
=learn  "SIMCLASSPROCBODY"%language for type declarations in begin blocks in class procedure%$

prefix  "BOOLEAN"   5 	 "BOOLEAN" . parselist(10,!'|,|) $
prefix  "INTEGER"   5 	 "INTEGER" . parselist(10,!'|,|) $
prefix  "REAL"      5	 "REAL"    . parselist(10,!'|,|) $
prefix  "REF"       5	 ("REF" . if newcheck(token,!'|(|)
	                           then (advance; getvarlist & check !'|)|)) .
			           parselist(10,!'|,|)$
prefix  "CHARACTER" 5 	 "CHARACTER" . parselist(10,!'|,|) $
prefix  "TEXT"      5	 "TEXT" . parselist(10,!'|,|) $

prefix  "PROCEDURE" 0 
"DEFSIMPROC" . (TOKEN & ADVANCE)  .
              (if newcheck(token,!'|(|)
                then (advance; PARSELIST(0,!'|,|) & check !'|)|) & check !'|;| ) .
             (check "BEGIN";
		    "BEGIN-INTERNAL" .
		    (if newcheck(token,"END") then nil else DEPROGNIFY(RIGHT))
		    & check "END") .
             "DEFUN-METHOD" .
             [?*CLASS?*]$

%================================================================%$
=learn "SIMARRDEC" %language for array declarations%$
define "PARSELIST1" (rb,delims);
       parse rb . if newcheck(token,delims) then (advance; parselist1(rb, delims))$

delim   !|:| $

infixd	"["	30 0     LEFT . PARSELIST1(0,!'(|:| |,|)) & check "]"$

=EXIT$

