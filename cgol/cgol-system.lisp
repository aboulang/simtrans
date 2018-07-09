;;; -*- Mode: LISP -*-

(defpackage cgol)

;cbef
;caft
;cparse
;cgol is cbef | cparse
;ctest is cbef | caft
;cgprin

(defsystem cgol
  (:default-pathname "conger:>lmlib>cgol>")
  (:serial "cbef" "caft" "cparse" ))