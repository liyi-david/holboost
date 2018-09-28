import abc

class CommandResult(abc.ABC):
    pass


class TermResult(CommandResult):
    def __init__(self, term):
        self.term = term


class StringResult(CommandResult):
    def __init__(self, string):
        self.string = string


class ListResult(CommandResult):
    def __init__(self, lst):
        self.lst = lst

class DictResult(CommandResult):
    def __init__(self, dict):
        self.dict = dict


class EmptyResult(CommandResult):
    def __init__(self):
        pass
