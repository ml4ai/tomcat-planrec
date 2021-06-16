; Example domain for testing

(define
    (domain construction)
    (:requirements :strips :typing)
    (:types
        site material - object
        bricks cables windows - material
    )
    (:constants mainsite - site)

    (:predicates
        (walls-built ?s - site)
        (windows-fitted ?s - site)
        (foundations-set ?s - site)
        (cables-installed ?s - site)
        (site-built ?s - site)
        (on-site ?m - material ?s - site)
        (material-used ?m - material)
    )

    (:action BUILD-WALL
        :parameters (?s - site ?b - bricks)
        :precondition (a ?x ?y)
        ;:precondition (and
            ;(on-site ?b ?s)
            ;(foundations-set ?s)
            ;(not (walls-built ?s))
            ;(not (material-used ?b))
        ;)
        ;:effect (and
            ;(walls-built ?s)
            ;(material-used ?b)
        ;)
    )

    (:action TRANSPORT_PURCHASES
        :parameters (?m - material ?factory ?house - site)
        :precondition (on-site ?m ?factory)
        ;:effect (and (not (on-site ?m ?factory))
                     ;(on-site ?m ?house))
    )
)
