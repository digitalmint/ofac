// Copyright 2020 The Moov Authors
// Use of this source code is governed by an Apache License
// license that can be found in the LICENSE file.

package main

import (
	"fmt"
	"math"
	"net/http/httptest"
	"net/url"
	"strings"
	"testing"

	"github.com/moov-io/watchman/pkg/csl"
	"github.com/moov-io/watchman/pkg/dpl"
	"github.com/moov-io/watchman/pkg/ofac"

	"github.com/go-kit/kit/log"
)

var (
	addressSearcher = &searcher{
		Addresses: precomputeAddresses([]*ofac.Address{
			{
				EntityID:                    "173",
				AddressID:                   "129",
				Address:                     "Ibex House, The Minories",
				CityStateProvincePostalCode: "London EC3N 1DY",
				Country:                     "United Kingdom",
			},
			{
				EntityID:                    "735",
				AddressID:                   "447",
				Address:                     "Piarco Airport",
				CityStateProvincePostalCode: "Port au Prince",
				Country:                     "Haiti",
			},
		}),
		pipe: noLogPipeliner,
	}
	altSearcher = &searcher{
		Alts: precomputeAlts([]*ofac.AlternateIdentity{
			{ // Real OFAC entry
				EntityID:      "559",
				AlternateID:   "481",
				AlternateType: "aka",
				AlternateName: "CIMEX",
			},
			{
				EntityID:      "4691",
				AlternateID:   "3887",
				AlternateType: "aka",
				AlternateName: "A.I.C. SOGO KENKYUSHO",
			},
		}),
		pipe: noLogPipeliner,
	}
	sdnSearcher = &searcher{
		SDNs: precomputeSDNs([]*ofac.SDN{
			{
				EntityID: "2676",
				SDNName:  "AL ZAWAHIRI, Dr. Ayman",
				SDNType:  "individual",
				Programs: []string{"SDGT", "SDT"},
				Title:    "Operational and Military Leader of JIHAD GROUP",
				Remarks:  "DOB 19 Jun 1951; POB Giza, Egypt; Passport 1084010 (Egypt); alt. Passport 19820215; Operational and Military Leader of JIHAD GROUP.",
			},
			{
				EntityID: "2681",
				SDNName:  "HAWATMA, Nayif",
				SDNType:  "individual",
				Programs: []string{"SDT"},
				Title:    "Secretary General of DEMOCRATIC FRONT FOR THE LIBERATION OF PALESTINE - HAWATMEH FACTION",
				Remarks:  "DOB 1933; Secretary General of DEMOCRATIC FRONT FOR THE LIBERATION OF PALESTINE - HAWATMEH FACTION.",
			},
		}, nil, noLogPipeliner),
		pipe: noLogPipeliner,
	}
	idSearcher = &searcher{
		SDNs: precomputeSDNs([]*ofac.SDN{
			{
				EntityID: "22790",
				SDNName:  "MADURO MOROS, Nicolas",
				SDNType:  "individual",
				Programs: []string{"VENEZUELA"},
				Title:    "President of the Bolivarian Republic of Venezuela",
				Remarks:  "DOB 23 Nov 1962; POB Caracas, Venezuela; citizen Venezuela; Gender Male; Cedula No. 5892464 (Venezuela); President of the Bolivarian Republic of Venezuela.",
			},
		}, nil, noLogPipeliner),
		pipe: noLogPipeliner,
	}
	dplSearcher = &searcher{
		DPs: precomputeDPs([]*dpl.DPL{
			{
				Name:           "AL NASER WINGS AIRLINES",
				StreetAddress:  "P.O. BOX 28360",
				City:           "DUBAI",
				State:          "",
				Country:        "AE",
				PostalCode:     "",
				EffectiveDate:  "06/05/2019",
				ExpirationDate: "12/03/2019",
				StandardOrder:  "Y",
				LastUpdate:     "2019-06-12",
				Action:         "FR NOTICE ADDED, TDO RENEWAL, F.R. NOTICE ADDED, TDO RENEWAL ADDED, TDO RENEWAL ADDED, F.R. NOTICE ADDED",
				FRCitation:     "82 F.R. 61745 12/29/2017,  83F.R. 28801 6/21/2018, 84 F.R. 27233 6/12/2019",
			},
			{
				Name:           "PRESTON JOHN ENGEBRETSON",
				StreetAddress:  "12725 ROYAL DRIVE",
				City:           "STAFFORD",
				State:          "TX",
				Country:        "US",
				PostalCode:     "77477",
				EffectiveDate:  "01/24/2002",
				ExpirationDate: "01/24/2027",
				StandardOrder:  "Y",
				LastUpdate:     "2002-01-28",
				Action:         "STANDARD ORDER",
				FRCitation:     "67 F.R. 7354 2/19/02 66 F.R. 48998 9/25/01 62 F.R. 26471 5/14/97 62 F.R. 34688 6/27/97 62 F.R. 60063 11/6/97 63 F.R. 25817 5/11/98 63 F.R. 58707 11/2/98 64 F.R. 23049 4/29/99",
			},
		}, noLogPipeliner),
		pipe: noLogPipeliner,
	}
	ssiSearcher = &searcher{
		SSIs: precomputeSSIs([]*csl.SSI{
			{
				EntityID:       "18782",
				Type:           "Entity",
				Programs:       []string{"SYRIA", "UKRAINE-EO13662"},
				Name:           "ROSOBORONEKSPORT OAO",
				Addresses:      []string{"27 Stromynka ul., Moscow, 107076, RU"},
				Remarks:        []string{"For more information on directives, please visit the following link: http://www.treasury.gov/resource-center/sanctions/Programs/Pages/ukraine.aspx#directives", "(Linked To: ROSTEC)"},
				AlternateNames: []string{"RUSSIAN DEFENSE EXPORT ROSOBORONEXPORT", "KENKYUSHO", "ROSOBORONEXPORT JSC", "ROSOBORONEKSPORT OJSC", "OJSC ROSOBORONEXPORT", "ROSOBORONEXPORT"},
				IDsOnRecord:    []string{"1117746521452, Registration ID", "56467052, Government Gazette Number", "7718852163, Tax ID No.", "Subject to Directive 3, Executive Order 13662 Directive Determination -", "www.roe.ru, Website"},
				SourceListURL:  "http://bit.ly/1QWTIfE",
				SourceInfoURL:  "http://bit.ly/1MLgou0",
			},
			{
				EntityID:       "18736",
				Type:           "Entity",
				Programs:       []string{"UKRAINE-EO13662"},
				Name:           "VTB SPECIALIZED DEPOSITORY, CJSC",
				Addresses:      []string{"35 Myasnitskaya Street, Moscow, 101000, RU"},
				Remarks:        []string{"For more information on directives, please visit the following link: http://www.treasury.gov/resource-center/sanctions/Programs/Pages/ukraine.aspx#directives", "(Linked To: ROSTEC)"},
				AlternateNames: []string{"CJS VTB SPECIALIZED DEPOSITORY"},
				IDsOnRecord:    []string{"1117746521452, Registration ID", "56467052, Government Gazette Number", "7718852163, Tax ID No.", "Subject to Directive 3, Executive Order 13662 Directive Determination -", "www.roe.ru, Website"},
				SourceListURL:  "http://bit.ly/1QWTIfE",
				SourceInfoURL:  "http://bit.ly/1MLgou0",
			},
		}, noLogPipeliner),
		pipe: noLogPipeliner,
	}
	bisEntitySearcher = &searcher{
		BISEntities: precomputeBISEntities([]*csl.EL{
			{
				Name:               "Mohammad Jan Khan Mangal",
				AlternateNames:     []string{"Air I"},
				Addresses:          []string{"Kolola Pushta, Charahi Gul-e-Surkh, Kabul, AF", "Maidan Sahr, Hetefaq Market, Paktiya, AF"},
				StartDate:          "11/13/19",
				LicenseRequirement: "For all items subject to the EAR (See ¬ß744.11 of the EAR). ",
				LicensePolicy:      "Presumption of denial.",
				FRNotice:           "81 FR 57451",
				SourceListURL:      "http://bit.ly/1L47xrV",
				SourceInfoURL:      "http://bit.ly/1L47xrV",
			},
			{
				Name:               "Luqman Yasin Yunus Shgragi",
				AlternateNames:     []string{"Lkemanasel Yosef", "Luqman Sehreci."},
				Addresses:          []string{"Savcili Mahalesi Turkmenler Caddesi No:2, Sahinbey, Gaziantep, TR", "Sanayi Mahalesi 60214 Nolu Caddesi No 11, SehitKamil, Gaziantep, TR"},
				StartDate:          "8/23/16",
				LicenseRequirement: "For all items subject to the EAR.  (See ¬ß744.11 of the EAR)",
				LicensePolicy:      "Presumption of denial.",
				FRNotice:           "81 FR 57451",
				SourceListURL:      "http://bit.ly/1L47xrV",
				SourceInfoURL:      "http://bit.ly/1L47xrV",
			},
		}, noLogPipeliner),
		pipe: noLogPipeliner,
	}
)

func TestBrobits(t *testing.T) {
	cases := []struct {
		s1, s2 string
		match  float64
	}{
		{"dariana lowe", "DARIAN, Tenny", 0.942},
	}
	for i := range cases {
		v := cases[i]
		// Only need to call chomp on s1, see jaroWinkler doc
		eql(t, fmt.Sprintf("#%d %s vs %s", i, v.s1, v.s2), jaroWinkler(v.s1, v.s2), v.match)
	}
}

func TestJaroWinkler(t *testing.T) {
	cases := []struct {
		s1, s2 string
		match  float64
	}{
		{"wei, zhao", "wei, Zhao", 0.942},
		{"WEI, Zhao", "WEI, Zhao", 1.0},
		{"WEI Zhao", "WEI Zhao", 1.0},
		{strings.ToLower("WEI Zhao"), precompute("WEI, Zhao"), 1.0},
		// make sure jaroWinkler is communative
		{"jane doe", "jan lahore", 0.471},
		{"jan lahore", "jane doe", 0.707},
		// real world case
		{"john doe", "paul john", 0.764},
		{"john doe", "john othername", 0.764},
		// close match
		{"jane doe", "jane doe2", 0.971},
		// real-ish world examples
		{"kalamity linden", "kala limited", 0.771},
		{"kala limited", "kalamity linden", 0.771},
		// examples used in demos / commonly
		{"nicolas", "nicolas", 1.0},
		{"nicolas moros maduro", "nicolas maduro", 1.0},
		{"nicolas maduro", "nicolas moros maduro", 1.0},
		// example cases
		{"nicolas maduro", "nicolas maduro", 1.0},
		{"maduro, nicolas", "maduro, nicolas", 1.0},
		{"maduro moros, nicolas", "maduro moros, nicolas", 1.0},
		{"maduro moros, nicolas", "nicolas maduro", 1.0},
		{"nicolas maduro moros", "nicolás maduro", 0.961},
		{"nicolas, maduro moros", "nicolas maduro", 0.988},
		{"nicolas, maduro moros", "nicolás maduro", 0.950},
		// stopwords
		{"i c sogo kenkyusho", precompute("A.I.C. SOGO KENKYUSHO"), 1.0},
		{precompute("A.I.C. SOGO KENKYUSHO"), "sogo kenkyusho", 1.0},
	}
	for i := range cases {
		v := cases[i]
		// Only need to call chomp on s1, see jaroWinkler doc
		eql(t, fmt.Sprintf("#%d %s vs %s", i, v.s1, v.s2), jaroWinkler(v.s1, v.s2), v.match)
	}
}

func TestJaroWinklerErr(t *testing.T) {
	v := jaroWinkler("", "hello")
	eql(t, "NaN #1", v, 0.0)

	v = jaroWinkler("hello", "")
	eql(t, "NaN #1", v, 0.0)
}

func eql(t *testing.T, desc string, x, y float64) {
	t.Helper()
	if math.IsNaN(x) || math.IsNaN(y) {
		t.Fatalf("%s: x=%.2f y=%.2f", desc, x, y)
	}
	if math.Abs(x-y) > 0.01 {
		t.Errorf("%s: %.3f != %.3f", desc, x, y)
	}
}

func TestEql(t *testing.T) {
	eql(t, "", 0.1, 0.1)
	eql(t, "", 0.0001, 0.00002)
}

// TestSearch_liveData will download the real data and run searches against the corpus.
// This test is designed to tweak match percents and results.
func TestSearch_liveData(t *testing.T) {
	if testing.Short() {
		return
	}
	searcher := &searcher{
		logger: log.NewNopLogger(),
		pipe:   noLogPipeliner,
	}
	if stats, err := searcher.refreshData(""); err != nil {
		t.Fatal(err)
	} else {
		searcher.logger.Log("liveData", fmt.Sprintf("stats: %#v", stats))
	}

	cases := []struct {
		name  string
		match float64 // top match %
	}{
		{"Nicolas MADURO", 1.0},
		{"nicolas maduro", 1.0},
	}
	for i := range cases {
		sdns := searcher.TopSDNs(1, cases[i].name)
		if len(sdns) == 0 {
			t.Errorf("name=%q got no results", cases[i].name)
		}
		eql(t, fmt.Sprintf("%q (SDN=%s) matches %q ", cases[i].name, sdns[0].EntityID, sdns[0].name), sdns[0].match, cases[i].match)
	}
}

func TestSearch__topAddressesAddress(t *testing.T) {
	it := topAddressesAddress("needle")(&Address{address: "needleee"})

	eql(t, "topAddressesAddress", it.weight, 0.950)
	if add, ok := it.value.(*Address); !ok || add.address != "needleee" {
		t.Errorf("got %#v", add)
	}
}

func TestSearch__topAddressesCountry(t *testing.T) {
	it := topAddressesAddress("needle")(&Address{address: "needleee"})

	eql(t, "topAddressesCountry", it.weight, 0.950)
	if add, ok := it.value.(*Address); !ok || add.address != "needleee" {
		t.Errorf("got %#v", add)
	}
}

func TestSearch__multiAddressCompare(t *testing.T) {
	it := multiAddressCompare(
		topAddressesAddress("needle"),
		topAddressesCountry("other"),
	)(&Address{address: "needlee", country: "other"})

	eql(t, "multiAddressCompare", it.weight, 0.986)
	if add, ok := it.value.(*Address); !ok || add.address != "needlee" || add.country != "other" {
		t.Errorf("got %#v", add)
	}
}

func TestSearch__extractSearchLimit(t *testing.T) {
	// Too high, fallback to hard max
	req := httptest.NewRequest("GET", "/?limit=1000", nil)
	if limit := extractSearchLimit(req); limit != hardResultsLimit {
		t.Errorf("got limit of %d", limit)
	}

	// No limit, use default
	req = httptest.NewRequest("GET", "/", nil)
	if limit := extractSearchLimit(req); limit != softResultsLimit {
		t.Errorf("got limit of %d", limit)
	}

	// Between soft and hard max
	req = httptest.NewRequest("GET", "/?limit=25", nil)
	if limit := extractSearchLimit(req); limit != 25 {
		t.Errorf("got limit of %d", limit)
	}

	// Lower than soft max
	req = httptest.NewRequest("GET", "/?limit=1", nil)
	if limit := extractSearchLimit(req); limit != 1 {
		t.Errorf("got limit of %d", limit)
	}
}

func TestSearch__addressSearchRequest(t *testing.T) {
	u, _ := url.Parse("https://moov.io/search?address=add&city=new+york&state=ny&providence=prov&zip=44433&country=usa")
	req := readAddressSearchRequest(u)
	if req.Address != "add" {
		t.Errorf("req.Address=%s", req.Address)
	}
	if req.City != "new york" {
		t.Errorf("req.City=%s", req.City)
	}
	if req.State != "ny" {
		t.Errorf("req.State=%s", req.State)
	}
	if req.Providence != "prov" {
		t.Errorf("req.Providence=%s", req.Providence)
	}
	if req.Zip != "44433" {
		t.Errorf("req.Zip=%s", req.Zip)
	}
	if req.Country != "usa" {
		t.Errorf("req.Country=%s", req.Country)
	}
	if req.empty() {
		t.Error("req is not empty")
	}

	req = addressSearchRequest{}
	if !req.empty() {
		t.Error("req is empty now")
	}
	req.Address = "1600 1st St"
	if req.empty() {
		t.Error("req is not empty now")
	}
}

func TestSearch__FindAddresses(t *testing.T) {
	addresses := addressSearcher.FindAddresses(1, "173")
	if v := len(addresses); v != 1 {
		t.Fatalf("len(addresses)=%d", v)
	}
	if addresses[0].EntityID != "173" {
		t.Errorf("got %#v", addresses[0])
	}
}

func TestSearch__TopAddresses(t *testing.T) {
	addresses := addressSearcher.TopAddresses(1, "Piarco Air")
	if len(addresses) == 0 {
		t.Fatal("empty Addresses")
	}
	if addresses[0].Address.EntityID != "735" {
		t.Errorf("%#v", addresses[0].Address)
	}
}

func TestSearch__TopAddressFn(t *testing.T) {
	addresses := addressSearcher.TopAddressesFn(1, topAddressesCountry("United Kingdom"))
	if len(addresses) == 0 {
		t.Fatal("empty Addresses")
	}
	if addresses[0].Address.EntityID != "173" {
		t.Errorf("%#v", addresses[0].Address)
	}
}

func TestSearch__FindAlts(t *testing.T) {
	alts := altSearcher.FindAlts(1, "559")
	if v := len(alts); v != 1 {
		t.Fatalf("len(alts)=%d", v)
	}
	if alts[0].EntityID != "559" {
		t.Errorf("got %#v", alts[0])
	}
}

func TestSearch__TopAlts(t *testing.T) {
	alts := altSearcher.TopAltNames(1, "SOGO KENKYUSHO")
	if len(alts) == 0 {
		t.Fatal("empty AltNames")
	}
	if alts[0].AlternateIdentity.EntityID != "4691" {
		t.Errorf("%#v", alts[0].AlternateIdentity)
	}
}

func TestSearch__FindSDN(t *testing.T) {
	sdn := sdnSearcher.FindSDN("2676")
	if sdn == nil {
		t.Fatal("nil SDN")
	}
	if sdn.EntityID != "2676" {
		t.Errorf("got %#v", sdn)
	}
}

func TestSearch__TopSDNs(t *testing.T) {
	sdns := sdnSearcher.TopSDNs(1, "Ayman ZAWAHIRI")
	if len(sdns) == 0 {
		t.Fatal("empty SDNs")
	}
	if sdns[0].EntityID != "2676" {
		t.Errorf("%#v", sdns[0].SDN)
	}
}

func TestSearch__TopDPs(t *testing.T) {
	dps := dplSearcher.TopDPs(1, "NASER AIRLINES")
	if len(dps) == 0 {
		t.Fatal("empty DPs")
	}
	// DPL doesn't have any entity IDs. Comparing expected address components instead
	if dps[0].DeniedPerson.StreetAddress != "P.O. BOX 28360" || dps[0].DeniedPerson.City != "DUBAI" {
		t.Errorf("%#v", dps[0].DeniedPerson)
	}
}

func TestSearcher_TopSSIs(t *testing.T) {
	ssis := ssiSearcher.TopSSIs(1, "ROSOBORONEKSPORT")
	if len(ssis) == 0 {
		t.Fatal("empty SSIs")
	}
	if ssis[0].SectoralSanction.EntityID != "18782" {
		t.Errorf("%#v", ssis[0].SectoralSanction)
	}
}

func TestSearcher_TopSSIs_limit(t *testing.T) {
	ssis := ssiSearcher.TopSSIs(2, "SPECIALIZED DEPOSITORY")
	if len(ssis) != 2 {
		t.Fatalf("Expected 2 results, found %d", len(ssis))
	}
	if ssis[0].SectoralSanction.EntityID != "18736" {
		t.Errorf("%#v", ssis[0].SectoralSanction)
	}
}

func TestSearcher_TopSSIs_reportAltNameWeight(t *testing.T) {
	ssis := ssiSearcher.TopSSIs(1, "KENKYUSHO")
	if len(ssis) == 0 {
		t.Fatal("empty SSIs")
	}
	if ssis[0].SectoralSanction.EntityID != "18782" {
		t.Errorf("%f - %#v", ssis[0].match, ssis[0].SectoralSanction)
	}
	if math.Abs(1.0-ssis[0].match) > 0.001 {
		t.Errorf("Expected match=1.0 for alt names: %f - %#v", ssis[0].match, ssis[0].SectoralSanction)
	}
}

func TestSearcher_TopBISEntities(t *testing.T) {
	els := bisEntitySearcher.TopBISEntities(1, "Khan")
	if len(els) == 0 {
		t.Fatal("empty ELs")
	}
	if els[0].Entity.Name != "Mohammad Jan Khan Mangal" {
		t.Errorf("%#v", els[0].Entity)
	}
}

func TestSearcher_TopBISEntities_AltName(t *testing.T) {
	els := bisEntitySearcher.TopBISEntities(1, "Luqman Sehreci.")
	if len(els) == 0 {
		t.Fatal("empty ELs")
	}
	if els[0].Entity.Name != "Luqman Yasin Yunus Shgragi" {
		t.Errorf("%#v", els[0].Entity)
	}
	if math.Abs(1.0-els[0].match) > 0.001 {
		t.Errorf("Expected match=1.0 for alt names: %f - %#v", els[0].match, els[0].Entity)
	}
}

func TestSearch__extractIDFromRemark(t *testing.T) {
	cases := []struct {
		input, expected string
	}{
		{"Cedula No. 10517860 (Venezuela);", "10517860"},
		{"National ID No. 22095919778 (Norway).", "22095919778"},
		{"Driver's License No. 180839 (Mexico);", "180839"},
		{"Immigration No. A38839964 (United States).", "A38839964"},
		{"C.R. No. 79190 (United Arab Emirates).", "79190"},
		{"Electoral Registry No. RZZVAL62051010M200 (Mexico).", "RZZVAL62051010M200"},
		{"Trade License No. GE0426505 (Italy).", "GE0426505"},
		{"Public Security and Immigration No. 98.805", "98.805"},
		{"Folio Mercantil No. 578349 (Panama).", "578349"},
		{"Trade License No. C 37422 (Malta).", "C 37422"},
		{"Moroccan Personal ID No. E 427689 (Morocco) issued 20 Mar 2001.", "E 427689"},
		{"National ID No. 5-5715-00025-50-6 (Thailand);", "5-5715-00025-50-6"},
		{"Trade License No. HRB94311.", "HRB94311"},
		{"Registered Charity No. 1040094.", "1040094"},
		{"Bosnian Personal ID No. 1005967953038;", "1005967953038"},
		{"Telephone No. 009613679153;", "009613679153"},
		{"Tax ID No. AABA 670850 Y.", "AABA 670850"},
		{"Phone No. 263-4-486946; Fax No. 263-4-487261.", "263-4-486946"},
		{"D-U-N-S Number 56-558-7594; V.A.T. Number MT15388917 (Malta); Trade License No. C 24129 (Malta); Company Number 4220856; Linked To: DEBONO, Darren.", "C 24129"}, // SDN 23410
	}
	for i := range cases {
		result := extractIDFromRemark(cases[i].input)
		if cases[i].expected != result {
			t.Errorf("input=%s expected=%s result=%s", cases[i].input, cases[i].expected, result)
		}
	}
}

func TestSearch__extractAKAsFromRemark(t *testing.T) {
	cases := []struct {
		input    string
		expected []string
	}{
		{"DOB 13 Jan 1967; alt. DOB 13 Jan 1970; POB Dushanbe, Tajikistan; Dealer and transporter of weapons and minerals; Owner, Great Lakes Business Company and Compagnie Aerienne des Grands; a.k.a. 'BONT'; a.k.a. 'BOUTOV'; a.k.a. 'BUTT'; a.k.a. 'BUTTE'.", []string{"bont", "boutov", "butt", "butte"}},
	}
	for i := range cases {
		results := extractAKAsFromRemark(cases[i].input)
		for n, result := range results {
			if cases[i].expected[n] != result {
				t.Errorf("input=%s expected=%s result=%s", cases[i].input, cases[i].expected[n], result)
			}
		}
	}
}

func TestSearch__FindSDNsByRemarksID(t *testing.T) {
	s := &searcher{
		SDNs: []*SDN{
			{
				SDN: &ofac.SDN{
					EntityID: "22790",
				},
				id: "Cedula No. C 5892464 (Venezuela);",
			},
			{
				SDN: &ofac.SDN{
					EntityID: "99999",
				},
				id: "Other",
			},
		},
	}

	sdns := s.FindSDNsByRemarksID(1, "5892464")
	if len(sdns) != 1 {
		t.Fatalf("sdns=%#v", sdns)
	}
	if sdns[0].EntityID != "22790" {
		t.Errorf("sdns[0].EntityID=%v", sdns[0].EntityID)
	}

	// successful multi-part match
	s.SDNs[0].id = "2456 7890"
	sdns = s.FindSDNsByRemarksID(1, "2456 7890")
	if len(sdns) != 1 {
		t.Fatalf("sdns=%#v", sdns)
	}
	if sdns[0].EntityID != "22790" {
		t.Errorf("sdns[0].EntityID=%v", sdns[0].EntityID)
	}

	// incomplete query (not enough numerical query parts)
	sdns = s.FindSDNsByRemarksID(1, "2456")
	if len(sdns) != 0 {
		t.Fatalf("sdns=%#v", sdns)
	}
	sdns = s.FindSDNsByRemarksID(1, "7890")
	if len(sdns) != 0 {
		t.Fatalf("sdns=%#v", sdns)
	}

	// query doesn't match
	sdns = s.FindSDNsByRemarksID(1, "12456")
	if len(sdns) != 0 {
		t.Fatalf("sdns=%#v", sdns)
	}

	// empty SDN remarks ID
	s.SDNs[0].id = ""
	sdns = s.FindSDNsByRemarksID(1, "12456")
	if len(sdns) != 0 {
		t.Fatalf("sdns=%#v", sdns)
	}

	// empty query
	sdns = s.FindSDNsByRemarksID(1, "")
	if len(sdns) != 0 {
		t.Fatalf("sdns=%#v", sdns)
	}
}
