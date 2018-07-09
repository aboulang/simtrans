;;; -*- Mode: LISP -*-


(defvar cgol-files
	'("conger:>lmlib>cgol>read-me.lisp"
	  "conger:>lmlib>cgol>cgol.info"	;documention
	  "conger:>lmlib>cgol>cgol.lisp"	;original source code, some of it
						;unfortunately written in CGOL itself
	  "conger:>lmlib>cgol>cbef.lisp"	;the LISP portion of cgol.lisp
	  "conger:>lmlib>cgol>caft.lisp"	;the CGOL portion of cgol.lisp (in lisp)
	  "conger:>lmlib>cgol>cgprin.lisp"))	;printer (LISP to CGOL)


(defpackage CGOL)

(defsystem CGOL
  (:pathname-default "conger:>lmlib>cgol>")
  (:module before "cbef")
  (:module after  "caft")
  (:compile-load before)
  (:compile-load after (:fasload before)))
