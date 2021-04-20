(ql:quickload "shop3")

(in-package :shop-user)
(defdomain (good-test-domain :type pddl-domain :redefine-ok T) (
  (:types
    agent
  )

  (:predicates
   (test)
   (A)
   (B)
   (C)
  )

  (:action do-A
   :parameters (?t - agent)
   :precondition ()
   :effect (A)
  )

  (:action do-B
   :parameters (?t - agent)
   :precondition ()
   :effect (B)
  )

  (:action do-C
   :parameters (?t - agent)
   :precondition ()
   :effect (C)
  )


  (:method (complete-task ?t)
    ()
    (:task !do-A ?t)
  )

  (:method (complete-task ?t)
    ()
    (:task !do-B ?t)
  )

  (:method (complete-task ?t)
    ()
    (:task !do-C ?t)
  )

))

(defproblem good-test-problem ((agent me) (test)) ((complete-task me)))

(find-plans 'good-test-problem :which :all :verbose :long-plans)
