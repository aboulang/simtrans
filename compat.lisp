;;; -*- Package: NET -*-

(eval-when (load eval compile)
(defsubst my-flavor (instance)
  (si:%instance-flavor instance))

(defsubst flavor (name)
  (get name 'si:flavor))


(defsubst flavor-get (flavor indicator)
  (get (locf (si:flavor-plist flavor)) indicator))
 
(defsubst flavor-put (flavor property indicator)
  (putprop (locf (si:flavor-plist flavor)) property indicator)))


;;;BASE FLAVOR FOR SIMULA OBJECT 
(defflavor sim-object () ()
  ;:special-instance-variables
   :settable-instance-variables
   :gettable-instance-variables)

(defmethod (sim-object :sim-send) (iv message-args)
  (if (listp message-args) (lexpr-send iv (car message-args) (cdr message-args))
      (send iv message-args)))

(defvar TRUE T)
(defvar FALSE NIL)
(defvar NONE NIL)
(defvar NOTEXT "")

(defvar *CLASS*)

(defvar *default-array-type* ':art-float)

(defconst *array-type-alist* '((real :art-q)    ;:art-float)
			       (integer :art-q) ;:art-32b)
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
      `(make-instance ',flavor-name ,@init-list))
    `(lexpr-funcall #'make-instance ',flavor-name (build-init-list ,flavor-name ,@args))))

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

;;;======================================;;;
;;;Classes etc. needed for compatibility ;;;
;;;======================================;;;

(defsubst blanks (num)
  (fillarray (make-array num ':type 'art-string) '(#\sp)))

;;(defsubst copy (string)
;;  (string-append string))

(defsubst copy (string)
  (intern-local string 'net))

(defsubst char (ch)
  ch)

(defflavor infile
	(pathname stream (lastitem nil) (endfile nil))
	()
  (:settable-instance-variables))

(eval-when (load eval compile)
(FLAVOR-PUT (FLAVOR 'infile) '(pathname) 'INIT-VARS))

(defmethod (infile :inimage) ()
  t)

(defmethod (infile :open) (width)
  (setq stream (if (string-equal pathname 'ME)
		   (setq stream standard-input)
		   (open pathname '(:in)))))

(defmethod (infile :close) ()
  (unless (string-equal pathname 'ME) (close stream)))

(defmethod (infile :inint) (&aux num)
  (setq num (read stream))
  (or (tyipeek nil stream nil)  (setq lastitem (setq endfile t)))
  num)

(defmethod (infile :inreal) (&aux num)
  (setq num (read stream))
  (or (tyipeek nil stream nil)  (setq lastitem (setq endfile t)))
  num)

(defmethod (infile :intext) (width &aux str)
  (setq str (loop for i from 1 to width
		  with curr-string = ""
		  do (string-append curr-string (send stream ':tyi))
		  finally (return curr-string)))
  (or (tyipeek nil stream nil) (setq lastitem (setq endfile t)))
  str)

(defmethod (infile :inchar) (&aux ch)
  (setq ch (send stream ':tyi))
  (if (member ch  '(#\cr #\lf #\page)) (setq ch (send self ':inchar)))
  (or (tyipeek nil stream nil) (setq lastitem (setq endfile t)))
  ch)

(defflavor outfile
	(pathname stream)
	()
  (:settable-instance-variables))

(eval-when (load eval compile)
(FLAVOR-PUT (FLAVOR 'outfile) '(pathname) 'INIT-VARS))

(defmethod (outfile :open) (width)
  (setq stream (if (string-equal pathname 'ME)
		   (setq stream standard-output)
		   (open pathname '(:out)))))

(defmethod (outfile :close) ()
  (unless (string-equal pathname 'ME) (close stream)))

(defmethod (outfile :outimage) ()
  (format stream "~%"))

(defmethod (outfile :breakoutimage) ()
  t)

(defmethod (outfile :outtext) (&rest strings)
  (format stream "~{~A~}" strings))

(defmethod (outfile :outchar) (char)
  (format stream "~A" char))

(defmethod (outfile :outint) (num width)
  (format:output stream
    (format:onum num 10. width)))

(defmethod (outfile :outreal) (num precision width)
  (format:output stream
    (format:ofloat num precision nil width)))

(defmethod (outfile :outfix) (num fract-precision width
				  &aux int-part fract-part int-width fract-width)
  (setq int-part (fix num))
  (setq fract-part (fix (+ (* (expt 10 fract-precision) (- num int-part)) 0.5)))
  (setq int-width (- width (if (= fract-precision 0) 0 (+ fract-precision 1))))
  (format:output stream
    (format:onum int-part 10. int-width))
  (when (> fract-precision 0)
    (setq fract-width (- (- width int-width) 1))
    (format:output stream "."
      (format:onum fract-part 10. fract-width ':pad-char #/0))))

(defmethod (outfile :setpos) (pos)
  (format:output stream
    (format:tab pos)))

;;;+++ This is hacked !!!
(defflavor scanner
	(stream (endoffile nil) (string "") (curpos 0))
	()
  (:settable-instance-variables))

(eval-when (load eval compile)
(FLAVOR-PUT (FLAVOR 'scanner) nil 'INIT-VARS))

(defmethod (scanner :readfrom) (stream1)
  (setq stream stream1))

(defmethod (scanner :set-ucaseon) (ignore)
  t)

(defmethod (scanner :readline) (&aux tstream)
  (setq tstream (send stream ':stream))
  (setq string (readline tstream))
  (setq curpos 0)
  (unless (send tstream ':operation-handled-p ':beep)
    (or (tyipeek nil tstream nil) (setq endoffile t))))

(defmethod (scanner :next) (&aux thing (newpos curpos))
  (with-input-from-string (tstream string newpos)
    (setq thing (read tstream ""))))

(defmethod (scanner :getnext) (&aux thing)
  (with-input-from-string (tstream string curpos)
    (setq thing (read tstream))))

(defmethod (scanner :getint) (ignore &aux num)
  (with-input-from-string (tstream string curpos)
    (setq num (read tstream))))

(defmethod (scanner :getreal) (ignore &aux num)
  (with-input-from-string (tstream string curpos)
    (setq num (read tstream))))

(defmethod (scanner :safegetint) (ignore &aux num)
  (with-input-from-string (tstream string curpos)
    (setq num (read tstream))))

(defmethod (scanner :safegetreal) (ignore &aux num)
  (with-input-from-string (tstream string curpos)
    (setq num (read tstream))))