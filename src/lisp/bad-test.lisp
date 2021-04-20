(ql:quickload "shop3")

(in-package :shop-user)
(defdomain (bad-test-domain :type pddl-domain :redefine-ok T) (
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
    A
    ()
    (:task !do-A ?t)

    B
    ()
    (:task !do-B ?t)

    C
    ()
    (:task !do-C ?t)
  )
))

(defproblem bad-test-problem ((agent me) (test)) ((complete-task me)))

(find-plans 'bad-test-problem :which :all :verbose :long-plans)
