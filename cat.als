sig Object {}

sig Morphism {
	from: one Object,
	to: one Object,
    comp: Morphism -> lone Morphism,
}

sig Cat {
    objects: set Object,
    morphisms: set Morphism,
}

fact {
    // All objects and morphisms belong to a category
    objects in Cat one -> Object
	morphisms in Cat one -> Morphism

    all cat: Cat {
        // Composition is only between matching morphisms
        all m1, m2, m3: cat.morphisms {
            (m2.comp[m1] = m3) => {
                m2.from = m1.to
                m3.from = m1.from
                m3.to = m2.to
            }
        }

        // There is always a composition if it is allowed
        all m1, m2: cat.morphisms | (m2.from = m1.to) => one m2.comp[m1]

        // Composition is associative
        all m1, m2, m3: cat.morphisms | (m3.comp[m2]).comp[m1] = m3.comp[m2.comp[m1]]

        // All Objects have an corresponding identity morphism
        all o: cat.objects | one identity[o]
    }
}

// Sends every object to it's identity morphism
fun identity: Object -> Morphism {
    { o: Object, id: Morphism | let cat = objects.o {
        id in cat.morphisms
        id.from = o && id.to = o
        all m: from.o | m.comp[id] = m
        all m: to.o | id.comp[m] = m
    }}
}

fun identity_of: Morphism -> Object {
    ~identity
}

fun morphism: Object -> Int -> Object {
    { o1: Object, num: Int, o2: Object | let cat = objects.o1 {
        o2 in cat.objects
        num = #{m: cat.morphisms | m.from = o1 && m.to = o2}
        num > 0
    }}
}


run { one Cat } for 3 but 5 Object, 5 Morphism, 5 Int
