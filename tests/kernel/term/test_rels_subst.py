from kernel.term import *
from unittest import TestCase

class TestRelsSubst(TestCase):

    def test_const(self):
        self.assertEqual(
                Const('sth').rels_subst([]),
                Const('sth')
                )

        self.assertEqual(
                Ind('Coq.Init.Datatypes.nat', 0).rels_subst([Rel(0), Rel(1)]),
                Ind('Coq.Init.Datatypes.nat', 0)
                )

    def test_bounded_variable(self):
        self.assertEqual(
                Lambda('x', Const('sometype'), Rel(0)).rels_subst(Const('a')),
                Lambda('x', Const('sometype'), Rel(0)),
                )

    def test_free_rels(self):
        pre = Lambda('x', Const('T'), Rel(2))
        post = Lambda('x', Const('T'), Rel(1))

        self.assertEqual(
                pre.rels_subst([Rel(2)]), post
                )
