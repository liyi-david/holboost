from os import listdir, path
from importlib import import_module

# the autoload function
def load():
    commands = {}
    proving_dir = listdir('proving')
    for name in proving_dir:
        # search for all subdirectories under `proving`
        dirname = path.join('proving', name)

        if path.isdir(dirname):
            for cmdname in listdir(dirname):
                # search for all python scripts under the sub-directory
                fullpath = path.join(dirname, cmdname)
                if path.isfile(fullpath) and fullpath.endswith(".py"):
                    mod = import_module(".".join(['proving', name, cmdname[:-3]]))
                    try:
                        if mod.autoload == True:
                            entry = getattr(mod, cmdname[:-3])
                            commands[cmdname[:-3]] = entry
                    except Exception:
                        # FIXME some kind of log?
                        pass


    return commands
