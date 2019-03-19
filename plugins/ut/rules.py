from kernel.macro import MacroFoldRule


class FoldUtWord(MacroFoldRule):
    @classmethod
    def fold(cls, t):

        # fold 1: word library for unit-verification
        _ut = "UnitVerify.Word."
        _ut_binoprs = {
                _ut + 'wplus'    : '+',
                _ut + 'wminus'  : '-',
                _ut + 'wmult'   : '*',
                _ut + 'wdiv'    : '/',
                _ut + 'wlt_bool': '<',
                _ut + 'wle_bool': '<=',
                _ut + 'wgt_bool': '>',
                _ut + 'wge_bool': '>=',
                _ut + 'weq_bool': '==',
                _ut + 'wne_bool': '!=',
                }

        if isinstance(t, Apply) and isinstance(t.func, Const) and t.func.name in _ut_binoprs:
            return cls(_ut_binoprs[t.func.name], t.args[2].fold(), t.args[3].fold())



