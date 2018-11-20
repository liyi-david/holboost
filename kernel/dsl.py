"""
the file defines a dsl framework which is used by the toploop and the plugin system. the framework
intends to support the following usage:

    program = {?c int a; a = 1; ?}

or something similar

"""

from abc import ABCMeta, abstractmethod, abstractclassmethod

class DSLParsingFailure(Exception):
    pass


class DSL(metaclass=ABCMeta):

    @staticmethod
    def unclosed_dsl(cmd):
        """
        check whether ther is a {? with no corresponding ?}.
        """
        in_dsl = False

        for i in range(len(cmd) - 1):
            if cmd[i:i + 2] == "{?":
                if in_dsl:
                    raise DSLParsingFailure("embedded DSL is not supported.")
                else:
                    in_dsl = True
            elif cmd[i:i + 2] == "?}":
                if in_dsl:
                    in_dsl = False
                else:
                    raise DLSParsingFailure("?} found before {?.")

        return in_dsl

    @staticmethod
    def preprocess(cmd):

        dsl_start_at = None
        dsl_last_end = -1
        new_cmd = ""

        for i in range(len(cmd) - 1):
            if cmd[i:i+2] == "{?":
                # dsl starts!
                if dsl_start_at is not None:
                    raise DSLParsingFailure("embedded DSL is not supported.")
                else:
                    # we just pass the dsl prefix `{?`
                    dsl_start_at = i + 2
                    new_cmd += cmd[dsl_last_end + 1:i]

            elif cmd[i:i+2] == "?}":
                # dsl ends!
                if dsl_start_at is None:
                    raise DLSParsingFailure("?} found before {?.")
                else:
                    # preprocessing the content inside {? ... ?}
                    dsl_content = cmd[dsl_start_at:i]
                    new_cmd += "DSL.get_parsed_object(%d)" % DSL.parse(dsl_content)
                    dsl_start_at = None
                    dsl_last_end = i + 1

        if dsl_start_at is not None:
            raise DSLParsingFailure("trying to parse an unfinished dsl block, a `?}` is missing.")

        new_cmd += cmd[dsl_last_end + 1:]
        return new_cmd



    # =========================================================================

    # dsl manager

    registered_dsls = {}

    @classmethod
    def register(cls):
        assert cls != DSL, "the abstract class DSL cannot register itself"
        assert isinstance(cls.name(), str), "invalid dsl name"
        assert cls.name() not in DSL.registered_dsls, "cannot register %s since the name is already registered." % cls.name()

        DSL.registered_dsls[cls.name()] = cls

    # =========================================================================

    # DSL interfaces and parsing object manager

    @abstractclassmethod
    def name(cls):
        pass

    __parsed_objects_lastid = -1
    __parsed_objects = {}

    @classmethod
    def parse(cls, content, env=None):
        assert cls == DSL, "any concrete DSL must overwrite this method to implement their own parsing behavior!"
        if env is None:
            from .environment import Environment
            env = Environment.default()

        # find the name of the dsl
        parts = content.split(" ", 1)
        dsl_name = parts[0]
        dsl_content = parts[1]

        if dsl_name not in cls.registered_dsls:
            raise DSLParsingFailure("unknown dsl %s" % dsl_name)
        else:
            result = cls.registered_dsls[dsl_name].parse(content, env)

        cls.__parsed_objects_lastid += 1
        cls.__parsed_objects[cls.__parsed_objects_lastid] = result
        return cls.__parsed_objects_lastid

    @classmethod
    def get_parsed_object(cls, ident):
        return cls.__parsed_objects[ident]
