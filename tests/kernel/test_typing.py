import unittest

from kernel.environment import Environment

env = Environment.default()

class TestTyping(unittest.TestCase):

    def test_nat_typing(self):
        nat = env['nat'].term()
        S = env['S'].term()
        O = env['O'].term()

        self.assertEqual(O.type(), nat)
