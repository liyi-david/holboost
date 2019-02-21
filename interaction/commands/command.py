# this file describe the abstract class of command

import abc
import importlib

class Command(abc.ABC):

    def __init__(self):
        self.task = None

    @classmethod
    def from_json(cls, json_item):
        assert cls == Command, 'you must rewrite from_json in %s' % str(cls)

        if json_item is None:
            return IdleCommand()
        else:
            submodule = json_item['name'].strip()
            subclassname = submodule.capitalize() + 'Command'
            subclass = getattr(
                    importlib.import_module("." + submodule, 'interaction.commands'),
                    subclassname
                    )
            return subclass.from_json(json_item)

    @abc.abstractmethod
    def run(self, top: 'Top'):
        pass

