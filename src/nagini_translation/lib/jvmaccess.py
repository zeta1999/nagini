"""
This Source Code Form is subject to the terms of the Mozilla Public
License, v. 2.0. If a copy of the MPL was not distributed with this
file, You can obtain one at http://mozilla.org/MPL/2.0/.
"""

import jpype


class JVM:
    """
    Encapsulates access to a JVM
    """

    def __init__(self, classpath: str):
        if not jpype.isJVMStarted():
            jpype.startJVM(jpype.getDefaultJVMPath(),
                           '-Djava.class.path=' + classpath, '-Xss128m')
        self.java = jpype.JPackage('java')
        self.scala = jpype.JPackage('scala')
        self.viper = jpype.JPackage('viper')
        self.fastparse = jpype.JPackage('fastparse')

    def get_proxy(self, supertype, instance):
        return jpype.JProxy(supertype, inst=instance)
