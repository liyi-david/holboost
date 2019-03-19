# this file describe the abstract class of command

import abc
import importlib

class Command(abc.ABC):

    is_trivial = True

    def __init__(self):
        self.task = None

    @classmethod
    def from_json(cls, json_item):
        assert cls == Command, 'you must rewrite from_json in %s' % str(cls)

        if json_item is None or 'name' not in json_item:
            json_item = {
                    'name': 'idle'
                    }

        classname = json_item['name'].strip()
        subclasses = cls.__subclasses__()
        matched_subclasses = list(filter(lambda c: c.__name__ == classname.capitalize() + "Command", subclasses))

        if len(matched_subclasses) == 0:
            raise Exception("unsupported command name %s." % classname)
        elif len(matched_subclasses) > 1:
            raise Exception("multiple matched command name %s." % classname)
        else:
            subclass = matched_subclasses[0]
            return subclass.from_json(json_item)

    @abc.abstractmethod
    def run(self, top: 'Top'):
        pass

