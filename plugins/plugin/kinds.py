from abc import ABCMeta, abstractmethod, abstractproperty

class Plugin(metaclass=ABCMeta):

    @abstractproperty
    def plugin_type(self) -> str:
        pass

    @abstractproperty
    def plugin_version(self) -> tuple:
        pass


class FrontendPlugin(Plugin):

    @property
    def plugin_type(self):
        return "frontend"

    @abstracproperty
    def grammar(self):
        pass
