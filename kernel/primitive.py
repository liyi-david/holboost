from kernel import term

class Numeric(term.Term):
    def __init__(self, value: 'int | float'):
        self.value = value

    def type(self):
        raise Exception('unimplemented')

    def export(self):
        return str(self.value)
