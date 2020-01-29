import java.util.List;

import javax.naming.Name;
import javax.naming.NamingException;
import javax.naming.directory.BasicAttributes;
import javax.naming.directory.DirContext;
import javax.naming.directory.InitialDirContext;
import javax.naming.directory.SearchControls;
import javax.naming.ldap.InitialLdapContext;
import javax.naming.ldap.LdapContext;
import javax.naming.ldap.LdapName;
import javax.naming.ldap.Rdn;

import com.unboundid.ldap.sdk.Filter;
import com.unboundid.ldap.sdk.LDAPConnection;
import com.unboundid.ldap.sdk.LDAPException;
import com.unboundid.ldap.sdk.LDAPSearchException;
import com.unboundid.ldap.sdk.ReadOnlySearchRequest;
import com.unboundid.ldap.sdk.SearchRequest;

import org.apache.directory.api.ldap.model.exception.LdapException;
import org.apache.directory.api.ldap.model.filter.EqualityNode;
import org.apache.directory.api.ldap.model.message.SearchRequestImpl;
import org.apache.directory.api.ldap.model.name.Dn;
import org.apache.directory.ldap.client.api.LdapConnection;
import org.apache.directory.ldap.client.api.LdapNetworkConnection;
import org.owasp.esapi.Encoder;
import org.owasp.esapi.reference.DefaultEncoder;
import org.springframework.ldap.core.LdapTemplate;
import org.springframework.ldap.filter.EqualsFilter;
import org.springframework.ldap.filter.HardcodedFilter;
import org.springframework.ldap.query.LdapQuery;
import org.springframework.ldap.query.LdapQueryBuilder;
import org.springframework.ldap.support.LdapEncoder;
import org.springframework.ldap.support.LdapNameBuilder;
import org.springframework.ldap.support.LdapUtils;
import org.springframework.web.bind.annotation.RequestParam;

public class LdapInjection {
  // JNDI
  public void testJndiBad1(@RequestParam String jBad, @RequestParam String jBadDN, DirContext ctx)
      throws NamingException {
    ctx.search("ou=system" + jBadDN, "(uid=" + jBad + ")", new SearchControls());
  }

  public void testJndiBad2(@RequestParam String jBad, @RequestParam String jBadDNName, InitialDirContext ctx)
      throws NamingException {
    ctx.search(new LdapName("ou=system" + jBadDNName), "(uid=" + jBad + ")", new SearchControls());
  }

  public void testJndiBad3(@RequestParam String jBad, @RequestParam String jOkDN, LdapContext ctx)
      throws NamingException {
    ctx.search(new LdapName(List.of(new Rdn("ou=" + jOkDN))), "(uid=" + jBad + ")", new SearchControls());
  }

  public void testJndiBad4(@RequestParam String jBadInitial, InitialLdapContext ctx)
      throws NamingException {
    ctx.search("ou=system", "(uid=" + jBadInitial + ")", new SearchControls());
  }

  public void testJndiBad5(@RequestParam String jBad, @RequestParam String jBadDNNameAdd, InitialDirContext ctx)
      throws NamingException {
    ctx.search(new LdapName("").addAll(new LdapName("ou=system" + jBadDNNameAdd)), "(uid=" + jBad + ")", new SearchControls());
  }

  public void testJndiBad6(@RequestParam String jBad, @RequestParam String jBadDNNameAdd2, InitialDirContext ctx)
      throws NamingException {
    LdapName name = new LdapName("");
    name.addAll(new LdapName("ou=system" + jBadDNNameAdd2).getRdns());
    ctx.search(new LdapName("").addAll(name), "(uid=" + jBad + ")", new SearchControls());
  }

  public void testJndiBad7(@RequestParam String jBad, @RequestParam String jBadDNNameToString, InitialDirContext ctx)
      throws NamingException {
    ctx.search(new LdapName("ou=system" + jBadDNNameToString).toString(), "(uid=" + jBad + ")", new SearchControls());
  }

  public void testJndiBad8(@RequestParam String jBad, @RequestParam String jBadDNNameClone, InitialDirContext ctx)
      throws NamingException {
    ctx.search((Name) new LdapName("ou=system" + jBadDNNameClone).clone(), "(uid=" + jBad + ")", new SearchControls());
  }

  public void testJndiOk1(@RequestParam String jOkFilterExpr, DirContext ctx) throws NamingException {
    ctx.search("ou=system", "(uid={0})", new String[] { jOkFilterExpr }, new SearchControls());
  }

  public void testJndiOk2(@RequestParam String jOkAttribute, DirContext ctx) throws NamingException {
    ctx.search("ou=system", new BasicAttributes(jOkAttribute, jOkAttribute));
  }

  // UnboundID
  public void testUnboundBad1(@RequestParam String uBad, @RequestParam String uBadDN, LDAPConnection c)
      throws LDAPSearchException {
    c.search(null, "ou=system" + uBadDN, null, null, 1, 1, false, "(uid=" + uBad + ")");
  }

  public void testUnboundBad2(@RequestParam String uBadFilterCreate, LDAPConnection c) throws LDAPException {
    c.search(null, "ou=system", null, null, 1, 1, false, Filter.create(uBadFilterCreate));
  }

  public void testUnboundBad3(@RequestParam String uBadROSearchRequest, @RequestParam String uBadROSRDN,
      LDAPConnection c) throws LDAPException {
    ReadOnlySearchRequest s = new SearchRequest(null, "ou=system" + uBadROSRDN, null, null, 1, 1, false,
        "(uid=" + uBadROSearchRequest + ")");
    c.search(s);
  }

  public void testUnboundBad4(@RequestParam String uBadSearchRequest, @RequestParam String uBadSRDN, LDAPConnection c)
      throws LDAPException {
    SearchRequest s = new SearchRequest(null, "ou=system" + uBadSRDN, null, null, 1, 1, false,
        "(uid=" + uBadSearchRequest + ")");
    c.search(s);
  }

  public void testUnboundBad5(@RequestParam String uBad, @RequestParam String uBadDNSFR, LDAPConnection c)
      throws LDAPSearchException {
    c.searchForEntry("ou=system" + uBadDNSFR, null, null, 1, false, "(uid=" + uBad + ")");
  }

  public void testUnboundBad6(@RequestParam String uBadROSearchRequestAsync, @RequestParam String uBadROSRDNAsync,
      LDAPConnection c) throws LDAPException {
    ReadOnlySearchRequest s = new SearchRequest(null, "ou=system" + uBadROSRDNAsync, null, null, 1, 1, false,
        "(uid=" + uBadROSearchRequestAsync + ")");
    c.asyncSearch(s);
  }

  public void testUnboundBad7(@RequestParam String uBadSearchRequestAsync, @RequestParam String uBadSRDNAsync, LDAPConnection c)
      throws LDAPException {
    SearchRequest s = new SearchRequest(null, "ou=system" + uBadSRDNAsync, null, null, 1, 1, false,
        "(uid=" + uBadSearchRequestAsync + ")");
    c.asyncSearch(s);
  }

  public void testUnboundBad8(@RequestParam String uBadFilterCreateNOT, LDAPConnection c) throws LDAPException {
    c.search(null, "ou=system", null, null, 1, 1, false, Filter.createNOTFilter(Filter.create(uBadFilterCreateNOT)));
  }

  public void testUnboundBad9(@RequestParam String uBadFilterCreateToString, LDAPConnection c) throws LDAPException {
    c.search(null, "ou=system", null, null, 1, 1, false, Filter.create(uBadFilterCreateToString).toString()); // False Negative
  }

  public void testUnboundBad10(@RequestParam String uBadFilterCreateToStringBuffer, LDAPConnection c) throws LDAPException {
    StringBuilder b = new StringBuilder();
    Filter.create(uBadFilterCreateToStringBuffer).toNormalizedString(b);
    c.search(null, "ou=system", null, null, 1, 1, false, b.toString());
  }
  
  public void testUnboundBad11(@RequestParam String uBadSearchRequestDuplicate, LDAPConnection c)
      throws LDAPException {
    SearchRequest s = new SearchRequest(null, "ou=system", null, null, 1, 1, false,
        "(uid=" + uBadSearchRequestDuplicate + ")");
    c.search(s.duplicate());
  }

  public void testUnboundBad12(@RequestParam String uBadROSearchRequestDuplicate, LDAPConnection c)
      throws LDAPException {
    ReadOnlySearchRequest s = new SearchRequest(null, "ou=system", null, null, 1, 1, false,
        "(uid=" + uBadROSearchRequestDuplicate + ")");
    c.search(s.duplicate());
  }

  public void testUnboundBad13(@RequestParam String uBadSearchRequestSetDN, LDAPConnection c)
      throws LDAPException {
    SearchRequest s = new SearchRequest(null, "", null, null, 1, 1, false, "");
    s.setBaseDN(uBadSearchRequestSetDN);
    c.search(s);
  }

  public void testUnboundBad14(@RequestParam String uBadSearchRequestSetFilter, LDAPConnection c)
      throws LDAPException {
    SearchRequest s = new SearchRequest(null, "ou=system", null, null, 1, 1, false, "");
    s.setFilter(uBadSearchRequestSetFilter);
    c.search(s);
  }

  public void testUnboundOk1(@RequestParam String uOkEqualityFilter, LDAPConnection c) throws LDAPSearchException {
    c.search(null, "ou=system", null, null, 1, 1, false, Filter.createEqualityFilter("uid", uOkEqualityFilter));
  }

  public void testUnboundOk2(@RequestParam String uOkVaragsAttr, LDAPConnection c) throws LDAPSearchException {
    c.search("ou=system", null, null, 1, 1, false, "(uid=fixed)", "a" + uOkVaragsAttr);
  }

  public void testUnboundOk3(@RequestParam String uOkFilterSearchRequest, LDAPConnection c) throws LDAPException {
    SearchRequest s = new SearchRequest(null, "ou=system", null, null, 1, 1, false,
        Filter.createEqualityFilter("uid", uOkFilterSearchRequest));
    c.search(s);
  }

  public void testUnboundOk4(@RequestParam String uOkSearchRequestVarargs, LDAPConnection c) throws LDAPException {
    SearchRequest s = new SearchRequest("ou=system", null, "(uid=fixed)", "va1", "va2", "va3",
        "a" + uOkSearchRequestVarargs);
    c.search(s);
  }

  // Spring LDAP
  public void testSpringBad1(@RequestParam String sBad, @RequestParam String sBadDN, LdapTemplate c) {
    c.search("ou=system" + sBadDN, "(uid=" + sBad + ")", 1, false, null);
  }

  public void testSpringBad2(@RequestParam String sBad, @RequestParam String sBadDNLNBuilder, LdapTemplate c) {
    c.authenticate(LdapNameBuilder.newInstance("ou=system" + sBadDNLNBuilder).build(), "(uid=" + sBad + ")", "pass");
  }

  public void testSpringBad3(@RequestParam String sBad, @RequestParam String sBadDNLNBuilderAdd, LdapTemplate c) {
    c.searchForObject(LdapNameBuilder.newInstance().add("ou=system" + sBadDNLNBuilderAdd).build(), "(uid=" + sBad + ")", null);
  }

  public void testSpringBad4(@RequestParam String sBadLdapQuery, LdapTemplate c) {
    c.findOne(LdapQueryBuilder.query().filter("(uid=" + sBadLdapQuery + ")"), null);
  }

  public void testSpringBad5(@RequestParam String sBadFilter, @RequestParam String sBadDNLdapUtils, LdapTemplate c) {
    c.find(LdapUtils.newLdapName("ou=system" + sBadDNLdapUtils), new HardcodedFilter("(uid=" + sBadFilter + ")"), null, null);
  }

  public void testSpringBad6(@RequestParam String sBadLdapQuery, LdapTemplate c) {
    c.searchForContext(LdapQueryBuilder.query().filter("(uid=" + sBadLdapQuery + ")"));
  }

  public void testSpringBad7(@RequestParam String sBadLdapQuery2, LdapTemplate c) {
    LdapQuery q = LdapQueryBuilder.query().filter("(uid=" + sBadLdapQuery2 + ")");
    c.searchForContext(q);
  }

  public void testSpringBad8(@RequestParam String sBadLdapQueryWithFilter, LdapTemplate c) {
    c.searchForContext(LdapQueryBuilder.query().filter(new HardcodedFilter("(uid=" + sBadLdapQueryWithFilter + ")")));
  }

  public void testSpringBad9(@RequestParam String sBadLdapQueryWithFilter2, LdapTemplate c) {
    org.springframework.ldap.filter.Filter f = new HardcodedFilter("(uid=" + sBadLdapQueryWithFilter2 + ")");
    c.searchForContext(LdapQueryBuilder.query().filter(f));
  }

  public void testSpringBad10(@RequestParam String sBadLdapQueryBase, LdapTemplate c) {
    c.find(LdapQueryBuilder.query().base(sBadLdapQueryBase).base(), null, null, null);
  }

  public void testSpringBad11(@RequestParam String sBadLdapQueryComplex, LdapTemplate c) {
    c.searchForContext(LdapQueryBuilder.query().base(sBadLdapQueryComplex).where("uid").is("test"));
  }

  public void testSpringBad12(@RequestParam String sBadFilterToString, LdapTemplate c) {
    c.search("", new HardcodedFilter("(uid=" + sBadFilterToString + ")").toString(), 1, false, null); // False Negative
  }

  public void testSpringBad13(@RequestParam String sBadFilterEncode, LdapTemplate c) {
    StringBuffer s = new StringBuffer();
    new HardcodedFilter("(uid=" + sBadFilterEncode + ")").encode(s);
    c.search("", s.toString(), 1, false, null);
  }

  public void testSpringOk1(@RequestParam String sOkLdapQuery, LdapTemplate c) {
    c.find(LdapQueryBuilder.query().filter("(uid={0})", sOkLdapQuery), null);
  }

  public void testSpringOk2(@RequestParam String sOkFilter, @RequestParam String sOkDN, LdapTemplate c) {
    c.find(LdapNameBuilder.newInstance().add("ou", sOkDN).build(), new EqualsFilter("uid", sOkFilter), null, null);
  }

  public void testSpringOk3(@RequestParam String sOkLdapQuery, @RequestParam String sOkPassword, LdapTemplate c) {
    c.authenticate(LdapQueryBuilder.query().filter("(uid={0})", sOkLdapQuery), sOkPassword);
  }

  // Apache LDAP API
  public void testApacheBad1(@RequestParam String aBad, @RequestParam String aBadDN, LdapConnection c)
      throws LdapException {
    c.search("ou=system" + aBadDN, "(uid=" + aBad + ")", null);
  }

  public void testApacheBad2(@RequestParam String aBad, @RequestParam String aBadDNObjToString, LdapNetworkConnection c)
      throws LdapException {
    c.search(new Dn("ou=system" + aBadDNObjToString).getName(), "(uid=" + aBad + ")", null); // False Negative
  }

  public void testApacheBad3(@RequestParam String aBadSearchRequest, LdapConnection c)
      throws LdapException {
    org.apache.directory.api.ldap.model.message.SearchRequest s = new SearchRequestImpl();
    s.setFilter("(uid=" + aBadSearchRequest + ")");
    c.search(s);
  }

  public void testApacheBad4(@RequestParam String aBadSearchRequestImpl, @RequestParam String aBadDNObj, LdapConnection c)
      throws LdapException {
    SearchRequestImpl s = new SearchRequestImpl();
    s.setBase(new Dn("ou=system" + aBadDNObj));
    c.search(s);
  }

  public void testApacheBad5(@RequestParam String aBadDNSearchRequestGet, LdapConnection c)
      throws LdapException {
    org.apache.directory.api.ldap.model.message.SearchRequest s = new SearchRequestImpl();
    s.setBase(new Dn("ou=system" + aBadDNSearchRequestGet));
    c.search(s.getBase(), "(uid=test", null);
  }

  public void testApacheOk1(@RequestParam String aOk, LdapConnection c)
      throws LdapException {
    org.apache.directory.api.ldap.model.message.SearchRequest s = new SearchRequestImpl();
    s.setFilter(new EqualityNode<String>("uid", aOk));
    c.search(s);
  }

  public void testApacheOk2(@RequestParam String aOk, LdapConnection c)
      throws LdapException {
    SearchRequestImpl s = new SearchRequestImpl();
    s.setFilter(new EqualityNode<String>("uid", aOk));
    c.search(s);
  }

  // ESAPI encoder sanitizer
  public void testOk3(@RequestParam String okEncodeForLDAP, DirContext ctx) throws NamingException {
    Encoder encoder = DefaultEncoder.getInstance();
    ctx.search("ou=system", "(uid=" + encoder.encodeForLDAP(okEncodeForLDAP) + ")", new SearchControls()); // False Positive
  }

  // Spring LdapEncoder sanitizer
  public void testOk4(@RequestParam String okFilterEncode, DirContext ctx) throws NamingException {
    ctx.search("ou=system", "(uid=" + LdapEncoder.filterEncode(okFilterEncode) + ")", new SearchControls()); // False Positive
  }

  // UnboundID Filter.encodeValue sanitizer
  public void testOk5(@RequestParam String okUnboundEncodeValue, DirContext ctx) throws NamingException {
    ctx.search("ou=system", "(uid=" + Filter.encodeValue(okUnboundEncodeValue) + ")", new SearchControls());
  }
}
