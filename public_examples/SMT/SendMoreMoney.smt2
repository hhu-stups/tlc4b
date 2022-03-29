; translated from Event-B with the PP approach of Rodin SMT Plugin
; and then added all different by hand and removed redundant bits

(set-info :status sat)
(set-logic AUFLIA)
(declare-fun D () Int)
(declare-fun E () Int)
(declare-fun M () Int)
(declare-fun N () Int)
(declare-fun O () Int)
(declare-fun R () Int)
(declare-fun S () Int)
(declare-fun Y () Int)


(assert (and 
            (<= 1 S) 
            (<= S 9)))
(assert (and 
            (<= 0 E) 
            (<= E 9)))
(assert (and 
            (<= 0 N) 
            (<= N 9)))
(assert (and 
            (<= 0 D) 
            (<= D 9)))
(assert (and 
            (<= 1 M) 
            (<= M 9)))
(assert (and 
            (<= 0 O) 
            (<= O 9)))
(assert (and 
            (<= 0 R) 
            (<= R 9)))
(assert (and 
            (<= 0 Y) 
            (<= Y 9)))
(assert (< 0 S))
(assert (< 0 M))
(assert (= (+ (* S 1000) (* E 100) (* N 10) D (* M 1000) (* O 100) (* R 10) E) (+ (* M 10000) (* O 1000) (* N 100) (* E 10) Y)))


(assert (not (= S E)))
(assert (not (= S N)))
(assert (not (= S D)))
(assert (not (= S M)))
(assert (not (= S O)))
(assert (not (= S R)))
(assert (not (= S Y)))

(assert (not (= E N)))
(assert (not (= E D)))
(assert (not (= E M)))
(assert (not (= E O)))
(assert (not (= E R)))
(assert (not (= E Y)))

(assert (not (= N D)))
(assert (not (= N M)))
(assert (not (= N O)))
(assert (not (= N R)))
(assert (not (= N Y)))


(assert (not (= D M)))
(assert (not (= D O)))
(assert (not (= D R)))
(assert (not (= D Y)))

(assert (not (= M O)))
(assert (not (= M R)))
(assert (not (= M Y)))

(assert (not (= O R)))
(assert (not (= O Y)))

(assert (not (= R Y)))
(check-sat)
(get-model)

