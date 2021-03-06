from __future__ import print_function
from charm.toolbox.pairinggroup import PairingGroup,ZR,G1,G2,GT,pair
from charm.toolbox.secretutil import SecretUtil
from charm.toolbox.schemebase import *

debug = False

class PoolComponent():
    lambda_prime_j, x_j, t_j, C_j_1, C_j_2, C_j_3 = None,None,None,None,None,None

class Pool():
    key, s, C0 = None,None,None
    poolComponents = []
    def view(self):
        print('#Pool:\n- key:',self.key,'\n- s:',self.s,'\n- C0:',self.C0,'\n- Components:')
        for each in self.poolComponents:
            print('  lambda:',each.lambda_prime_j)
            print('  x_j:',each.x_j)
            print('  t_j:',each.t_j)
            print('  Cj1:',each.C_j_1)
            print('  Cj2:',each.C_j_2)
            print('  Cj3:',each.C_j_3)
            print('\n')

    def appendComponent(self,component):
        self.poolComponents.append(component)

    def popComponent(self):
        try:
            return self.poolComponents.pop()
        except:
            return None

    def setKey(self, item):
        self.key = item

    def getKey(self):
        return self.key

    def setS(self, item):
        self.s = item

    def popS(self):
        try:
            S = self.s
            self.s = None
            return S
        except:
            return None

    def setC0(self, item):
        self.C0 = item

    def popC0(self):
        try:
            c0 = self.C0
            self.C0 = None
            return c0
        except:
            return None

class myABE(SchemeBase):
    pool = None
    def __init__(self, groupObj):
        SchemeBase.__init__(self)
        SchemeBase.setProperty(self, scheme='ABEnc')
        self.baseSecDefs = Enum('IND_AB_CPA', 'IND_AB_CCA', 'sIND_AB_CPA', 'sIND_AB_CCA')
        global util, group
        util = SecretUtil(groupObj, debug)
        group = groupObj
        self.pool = Pool()

    def setup(self):
        g1 = group.random(G1)
        g2 = group.random(G2)
        h = group.random(G2)
        u = group.random(G2)
        v = group.random(G2)
        w = group.random(G2)
        alpha = group.random()
        e_gg_alpha = pair(g1,g2) ** alpha
        pk = {'g1':g1, 'g2':g2, 'h':h, 'u':u, 'v':v, 'w':w, 'e(gg)^alpha':e_gg_alpha}
        msk = {'pk':pk, 'alpha':alpha}
        return (msk,pk)

    def keygen(self, msk, S):
        pk = msk['pk']
        attributes = [unicode(a) for a in S]
        z = group.random()
        r = group.random()
        K0 = ( (pk['g2'] ** msk['alpha']) * (pk['w'] ** r) ) ** (1/z)
        K1 = pk['g1'] ** (r/z)
        K_x_2, K_x_3 = {},{}
        for attr in attributes:
            ri = group.random()
            K_x_2[attr] = pk['g1']**(ri/z)
            K_x_3[attr] = ((pk['u']**group.hash(unicode(attr)))*pk['h'])**(ri/z) * pk['v']**(-r/z)
        ik = {'S':S, 'K0':K0, 'K1':K1, 'Ki2':K_x_2,'Ki3':K_x_3}
        sk = z

        return (ik,sk)

    # pre-encrypt P random offline components
    def pre_enc(self, pk, P):
        if self.pool.s == None or self.pool.getKey() == None or self.pool.C0 == None:
            s = group.random()
            self.pool.setS(s)
            self.pool.setKey(pk['e(gg)^alpha']**s)
            self.pool.setC0(pk['g1']**s)

        for j in range(P):
            component = PoolComponent()
            component.lambda_prime_j = group.random()
            component.t_j = group.random()
            component.x_j = group.random()
            component.C_j_1 = ((pk['w']**component.lambda_prime_j)*pk['v']**component.t_j)
            component.C_j_2 = (((pk['u']**component.x_j)*pk['h'])**(-component.t_j))
            component.C_j_3 = (pk['g1']**component.t_j)
            self.pool.appendComponent(component)

    def encrypt(self, pk, policy_str):
        policy = util.createPolicy(policy_str)
        sshares = util.calculateSharesList(self.pool.popS(), policy)
        sshares = dict([(x[0].getAttributeAndIndex(), x[1]) for x in sshares])
        C0 = self.pool.popC0()
        C_x_1, C_x_2, C_x_3, C_x_4, C_x_5 = {},{},{},{},{}
        for attr, s_share in sshares.items():
            k_attr = util.strip_index(attr)
            component = self.pool.popComponent()
            C_x_1[attr] = component.C_j_1
            C_x_2[attr] = component.C_j_2
            C_x_3[attr] = component.C_j_3
            C_x_4[attr] = s_share - component.lambda_prime_j
            C_x_5[attr] = component.t_j * (group.hash(unicode(attr)) - component.x_j)

        return {'policy':policy_str, 'C0':C0,'C_j_1':C_x_1, 'C_j_2':C_x_2, 'C_j_3':C_x_3, 'C_j_4':C_x_4, 'C_j_5':C_x_5}

    def pre_dec(self, pk, ik, ct):
        w = pk['w']
        u = pk['u']
        S = ik['S']
        K0 = ik['K0']
        K1 = ik['K1']
        Kj2 = ik['Ki2']
        Kj3 = ik['Ki3']
        C0 = ct['C0']
        Ci1 = ct['C_j_1']
        Ci2 = ct['C_j_2']
        Ci4 = ct['C_j_4']
        Ci5 = ct['C_j_5']
        Ci3 = ct['C_j_3']
        policy = util.createPolicy(ct['policy'])
        pruned = util.prune(policy, S)
        if pruned == False:
            return False
        wi = util.getCoefficients(policy) #wi = {u'TWO': <pairing.Element object at xxx>, u'FOUR': <pairing.Element object at xxx>}

        eC0K0 = pair(C0,K0)

        Ewi = 0
        moonlight = 1
        for i in pruned:
            index = i.getAttributeAndIndex()
            attr = i.getAttribute()

            Ewi += Ci4[index] * wi[index]

            eCi1K1 = pair(K1,Ci1[index])
            eCi2uCi5Kj2 = pair(Kj2[index],Ci2[index]*(u**(-Ci5[index])))
            eCi3Kj3 = pair(Ci3[index],Kj3[index])
            moonlight *= (eCi1K1 * eCi2uCi5Kj2 * eCi3Kj3) ** wi[index]

        ewEwiK1 = pair(K1,w**Ewi)
        return eC0K0/(ewEwiK1 * moonlight)

    def decrypt(self, sk, im):
        return im**sk

def main():
    #Get the eliptic curve with the bilinear mapping feature needed.
    groupObj = PairingGroup('SS512')
    my = myABE(groupObj)

    #Setup an authority
    auth_attrs= ['ONE', 'TWO', 'THREE', 'FOUR']

    (msk, pk) = my.setup()
    print('\n#msk:')
    for key,value in msk.items():
        print('- ',key,value,':')
        try:
            for x,y in value.items():
                print('\t',x,':',y)
        except:
            pass
    print('\n#pk:')
    for key,value in pk.items():
        print('- ',key,value,':')
        try:
            for x,y in value.items():
                print('\t',x,':',y)
        except:
            pass
    pol = '((ONE or THREE) and (TWO or FOUR))'
    attr_list = ['THREE', 'ONE', 'TWO']

    if debug: print('Acces Policy: %s' % pol)
    if debug: print('User credential list: %s' % attr_list)

    m = groupObj.random(GT)

    (ik,sk) = my.keygen(msk, attr_list)
    print("\nSecret key: %s" % attr_list)
    print('\n#ik:')
    for key,value in ik.items():
        print('- ',key,value,':')
        try:
            for x,y in value.items():
                print('\t',x,':',y)
        except:
            pass
    print('\n#sk:',sk)

    my.pre_enc(pk,10)
    my.pool.view()

    CT = my.encrypt(pk,pol)
    print('#ct:')
    for key,value in CT.items():
        print('- ',key,value,':')
        try:
            for x,y in value.items():
                print('\t',x,':',y)
        except:
            pass

    IM = my.pre_dec(pk,ik,CT)
    print('#im:',IM)

    orig_m = my.decrypt(sk,IM)
    print('#m`=',orig_m)
    print('#m =',m)
    del groupObj

if __name__ == '__main__':
    debug = False
    main()